theory Sim_Rules
imports Strong_CRef "CSimpl.SmallStepCon"
begin
section \<open>Operational rules for CSimpRGSim\<close>

lemma conjId: "\<lbrakk>Q; P\<rbrakk> \<Longrightarrow> P \<and> Q" by (rule conjI)


definition eq_rel:: "'a set \<Rightarrow> 'b set  \<Rightarrow>('a\<times>'b) set" 
  ("_ \<rightleftharpoons> / _" [81,81] 100) 
  where
"eq_rel s1 s2   \<equiv> {(a,b).  (a \<in> s1) = (b \<in> s2)}"

definition and_rel:: "'a set \<Rightarrow> 'b set  \<Rightarrow>('a\<times>'b) set" 
  ("_ \<odot> / _" [81,81] 100) 
  where
"and_rel s1 s2   \<equiv> {(a,b). (a \<in> s1) \<and> (b \<in> s2)}"

definition ext_set:: "('a\<times>'b) set  \<Rightarrow>(('a\<times>'a1) \<times>('b\<times>'b1)) set"  ("(\<up>_)" [1000] 999)
  where
"ext_set s1  \<equiv> {(a,b).  (fst a, fst b)\<in>s1}"

lemma same_set: 
  "(\<sigma>, \<Sigma>) \<in> \<xi> \<Longrightarrow>
   \<xi> \<subseteq> \<up>(b\<^sub>c \<rightleftharpoons>  b\<^sub>s) \<Longrightarrow> 
   (fst \<sigma> \<in> b\<^sub>c) = (fst \<Sigma> \<in> b\<^sub>s)" 
  unfolding eq_rel_def ext_set_def  by auto
 
lemma alpha_id_G:assumes 
  a0:"(\<sigma>,\<Sigma>) \<in> \<alpha>" and  
  a1:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>) \<in> G\<^sub>c"
shows "((\<sigma>, \<sigma>), \<Sigma>, \<Sigma>) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
 using a0 a1 unfolding  related_transitions_def Id_def  by fastforce
  

lemma skip3:
  assumes a0:"(\<sigma>, \<Sigma>) \<in> \<xi>" and                    
          a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>) \<in> G\<^sub>c" 
        shows 
           "(\<exists>\<Sigma>'. ((\<sigma>, \<sigma>), \<Sigma>, \<Sigma>') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
            (\<sigma>, \<Sigma>') \<in> \<xi> \<and>           
            \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Skip,  \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>*
                    (LanguageCon.com.Skip, \<Sigma>'))"  
  using a0 a1  a2  unfolding related_transitions_def Id_def 
  by fast

lemma skip4:
  assumes a0:"(\<sigma>, \<Sigma>) \<in> \<alpha>" and a1:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>) \<in> G\<^sub>c" 
        shows 
           "(\<exists>\<Sigma>'. ((\<sigma>, \<sigma>), \<Sigma>, \<Sigma>') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>                       
            \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Fault f,  \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, \<Sigma>'))"  
  using a0 a1   unfolding related_transitions_def Id_def 
  by fast



lemma term_RTC_not_change_state:
      assumes a0:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (c,  \<Sigma>) \<rightarrow>\<^sup>* (c, \<Sigma>')" and a1:"final (c,\<Sigma>)"
      shows "\<Sigma>=\<Sigma>'"
proof-
  have "(c, \<Sigma>) = (c, \<Sigma>') \<or> 
        (\<exists>c' \<Sigma>''. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (c,  \<Sigma>) \<rightarrow> (c', \<Sigma>'') \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (c',  \<Sigma>'') \<rightarrow>\<^sup>* (c, \<Sigma>'))"
    by (metis a0 converse_rtranclpE2 )
  moreover { assume "(c, \<Sigma>) = (c, \<Sigma>')"
    then have ?thesis by auto
  }
  moreover{
    assume "(\<exists>c' \<Sigma>''. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (c,  \<Sigma>) \<rightarrow> (c', \<Sigma>'') \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (c',  \<Sigma>'') \<rightarrow>\<^sup>* (c, \<Sigma>'))"
    then have ?thesis using a1 unfolding final_def
      by (meson SmallStepCon.no_step_final' a1 stepce_stepc)      
  }
  ultimately show ?thesis by auto   
qed



lemma Fault_sim:
  assumes  a1:"(\<sigma>, \<Sigma>) \<in> \<alpha>" and a2:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" 
  shows
   "(\<Gamma>\<^sub>c,(Fault f, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Fault f, \<Sigma>),R\<^sub>s,G\<^sub>s)"  
  using a1    
  apply(coinduction arbitrary: \<sigma> \<Sigma>)
  apply clarsimp
  apply (rule conjId)+
  apply (auto simp add: no_step_Fault)
   apply (auto simp add: related_transitions_def)
  by (auto simp add: a2 Domain.DomainI)


lemma Fault_s_sim:
  assumes  a1:"(\<sigma>, \<Sigma>) \<in> \<alpha>" and a2:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" 
  shows
   "(\<Gamma>\<^sub>c,(Fault f, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>s\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Fault f, \<Sigma>),R\<^sub>s,G\<^sub>s)" 
  using a1    
  apply(coinduction arbitrary: \<sigma> \<Sigma>)
  apply clarsimp
  apply (rule conjId)+          
      apply (auto simp add: no_step_Fault)    
  by (auto simp add: a2 Domain.DomainI related_transitions_def final_def 
      dest:  term_RTC_not_change_state)
 
lemma Stuck_sim:
  assumes  a1:"(\<sigma>, \<Sigma>) \<in> \<alpha>" and a2:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" 
  shows
   "(\<Gamma>\<^sub>c,(Stuck, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Stuck, \<Sigma>),R\<^sub>s,G\<^sub>s)" 
  using a1    
  apply(coinduction arbitrary: \<sigma> \<Sigma>)
  apply clarsimp
  apply (rule conjId)+
     apply (auto simp add: related_transitions_def)
  by (auto simp add: no_step_Stuck a2 Domain.DomainI)

lemma Stuck_s_sim:
  assumes  a1:"(\<sigma>, \<Sigma>) \<in> \<alpha>" and a2:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" 
  shows
   "(\<Gamma>\<^sub>c,(Stuck, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>s\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Stuck, \<Sigma>),R\<^sub>s,G\<^sub>s)" 
  using a1    
  apply(coinduction arbitrary: \<sigma> \<Sigma>)
  apply clarsimp
  apply (rule conjId)+
apply (auto simp add: no_step_Stuck)    
  by (auto simp add: a2 Domain.DomainI related_transitions_def final_def 
      dest:  term_RTC_not_change_state)

lemma sim_env:
  assumes 
 a0:"(\<sigma>, \<Sigma>) \<in> \<xi>" and
 a1:"Sta\<^sub>s \<xi> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>" and
 a2:" (((\<sigma>, \<sigma>'), \<Sigma>, \<Sigma>') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" 
shows" (\<sigma>', \<Sigma>') \<in> \<xi>"
  using a0 a1 a2  unfolding Sta\<^sub>s_def  by fastforce

lemma "\<xi> \<subseteq> \<alpha> \<Longrightarrow> (((a, b), ba), (aa, bb), bc) \<in> \<xi> \<Longrightarrow> Sta\<^sub>s \<xi> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow>
        \<forall>a b ba. (((a, b), ba), (a, b), ba) \<in> G\<^sub>c 
       \<Longrightarrow> \<forall>ab bd be ac bf bg.
              ((((a, b), ba), (ab, bd), be), ((aa, bb), bc), (ac, bf), bg) \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<longrightarrow>
              (((ab, bd), be), (ac, bf), bg) \<in> \<xi> \<or> (\<Gamma>\<^sub>c,(LanguageCon.com.Skip, (ab, bd), be),R\<^sub>c,G\<^sub>c)
              \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(LanguageCon.com.Skip, (ac, bf), bg),R\<^sub>s,G\<^sub>s)"
  using sim_env by auto
  
lemma skip_step: "\<xi> \<subseteq> \<alpha> \<Longrightarrow> (((a, b), ba), (aa, bb), bc) \<in> \<xi> \<Longrightarrow> Sta\<^sub>s \<xi> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow>
        \<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c \<Longrightarrow>
           \<exists>ab bd.
              ((((a, b), ba), (a, b), ba), ((aa, bb), bc), (ab, bd), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
              (((a, b), ba), (ab, bd), bc) \<in> \<xi> \<and>
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Skip, CRef.toSeq ((aa, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                      (LanguageCon.com.Skip, CRef.toSeq ((ab, bd), bc))"
  using related_transition_intro
  by (smt in_mono rtrancl.rtrancl_refl rtrancl_idemp rtranclp.rtrancl_refl Domain.DomainI)

 lemma Skip_sim:
  assumes a1:"\<xi> \<subseteq> \<alpha>" and
          a2: "(\<sigma>,\<Sigma>)\<in>\<xi>" and
          a3: "Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
          a5: "\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>) \<in> G\<^sub>c"  
  shows
   "(\<Gamma>\<^sub>c,(Skip, \<sigma>),R\<^sub>c,G\<^sub>c)
           \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Skip, \<Sigma>),R\<^sub>s,G\<^sub>s)" using  a1 a2 a3  a5 
  apply (coinduction arbitrary: \<sigma> \<Sigma>)
   apply (clarsimp)   
   apply (rule conjI,blast intro: skip1)+
   apply (rule conjI)
   apply (simp add: sim_env) 
   by (fast intro: skip_step)
 
lemma Skip_sound: 
  "\<xi> \<subseteq> \<alpha> \<Longrightarrow> Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow> \<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c \<Longrightarrow> 
    (\<Gamma>\<^sub>c,Skip,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,Skip,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def by (simp add: Skip_sim) 
        
 
lemma throw3:
  assumes a0:"(\<sigma>, \<Sigma>) \<in> \<xi>" and          
          a2:"\<xi> \<subseteq> \<alpha>" and a3:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>) \<in> G\<^sub>c" 
        shows 
           "(\<exists>\<Sigma>'. ((\<sigma>, \<sigma>), \<Sigma>, \<Sigma>') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
            (\<sigma>, \<Sigma>') \<in> \<xi> \<and> snd \<Sigma> = snd \<Sigma>' \<and>          
            \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Throw, toSeq \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, toSeq \<Sigma>'))"  
  using a0 a2 a3 unfolding related_transitions_def Id_def by fast   
  
lemma Throw_sim:
  assumes  a0:"\<xi> \<subseteq> \<alpha>" and
          a1: "(\<sigma>,\<Sigma>)\<in>\<xi>" and 
          a2: "Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
          a4: "\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" 
  shows
   "(\<Gamma>\<^sub>c,(Throw, \<sigma>),R\<^sub>c,G\<^sub>c)
           \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>) (\<Gamma>\<^sub>s,(Throw, \<Sigma>),R\<^sub>s,G\<^sub>s)" using  a0 a1 a2  a4
  apply (coinduction arbitrary: \<sigma> \<Sigma>)
  apply (clarsimp)
   apply (rule conjI,blast)
   apply (rule conjI, fastforce intro: throw1)        
  apply (rule conjI, metis (no_types, lifting) SmallStepCon.stepc_elim_cases(11) stepce_stepc)   
  apply (rule conjI, simp add:  sim_env)  
  by (frule throw3, auto)


        
lemma Throw_sound: 
  "\<xi> \<subseteq> \<alpha> \<Longrightarrow> Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow>  \<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>) \<in> G\<^sub>c \<Longrightarrow> 
   (\<Gamma>\<^sub>c,Throw,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>) (\<Gamma>\<^sub>s,Throw,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def by (simp add: Throw_sim )    
  
 lemma env_sim:
   assumes
     a0:" (\<Gamma>\<^sub>c,(c1\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" and
     a1:"((\<sigma>, s1), \<Sigma>, s1') \<in> ((R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" 
     shows"
          (\<Gamma>\<^sub>c,(c1\<^sub>c, s1),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1\<^sub>s, s1'),R\<^sub>s,G\<^sub>s)  \<or> P"   
using  dest_sim_env_step[OF a0 a1 ] by fastforce

lemma seq_ev_comp_step:
  assumes a0:"(\<Gamma>\<^sub>c,(c1\<^sub>c, (a, b), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1\<^sub>s, (aa, bb), bc),R\<^sub>s,G\<^sub>s)" and
        a1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Seq c1\<^sub>c c2\<^sub>c, toSeq ((a, b), ba)) \<rightarrow>(c\<^sub>c', toSeq ((ab, bd), ba))"
      shows "\<exists>c\<^sub>s' ac be.
              (\<exists>a ab b.
                  \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq c1\<^sub>s c2\<^sub>s, toSeq ((aa, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, (ab, b)) \<and>
                  (\<exists>aa ad ba.
                      \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, ab, b) \<rightarrow> (aa, ad, ba) \<and>
                      \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ad, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((ac, be), bc)))) \<and>
              (((ab, bd), ba), (ac, be), bc) \<in> \<alpha> \<and>
              ((((a, b), ba), (ab, bd), ba), ((aa, bb), bc), (ac, be), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
              ((\<exists>a b bb c1\<^sub>c.
                   c\<^sub>c' = Seq c1\<^sub>c c2\<^sub>c \<and>
                   (\<exists>c1\<^sub>s.
                       c\<^sub>s' = Seq c1\<^sub>s c2\<^sub>s \<and>
                       ac = a \<and>
                       be = b \<and>
                       bc = bb \<and> (\<Gamma>\<^sub>c,(c1\<^sub>c, (ab, bd), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) 
                               (\<Gamma>\<^sub>s,(c1\<^sub>s, (a, b), bb),R\<^sub>s,G\<^sub>s))) \<or>
               (\<Gamma>\<^sub>c,(c\<^sub>c', (ab, bd), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (ac, be), bc),R\<^sub>s,G\<^sub>s))"  
proof-
  have "c1\<^sub>c\<noteq>Skip \<and> c1\<^sub>c\<noteq>Throw" 
    using not_seq_skip_throw_ev  a1  by fast
  then obtain c1'
    where stepc1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (c1\<^sub>c, toSeq ((a, b), ba)) \<rightarrow> (c1', toSeq ((ab, bd), ba))" and 
          seq:    "(c\<^sub>c', ((ab, bd), ba))= (Seq c1' c2\<^sub>c,  ((ab, bd), ba))" 
    using stepc_elim_cases1(7)[OF a1, of "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (c1\<^sub>c, toSeq ((a, b), ba)) \<rightarrow> 
                                                      (c1', toSeq ((ab, bd), ba)) \<and> 
                                          (c\<^sub>c', toSeq ((ab, bd), ba))= 
                                          (Seq c1' c2\<^sub>c, toSeq ((ab, bd), ba))"]
    by fastforce
  thus ?thesis 
    using  seq_ev_plus stepc1 seq  dest_sim_ev_step[OF a0 stepc1]
    by fastforce
qed    

   (*if c1\<^sub>c = Skip and \<sigma> is not normal we cannot get  (\<Gamma>\<^sub>c,c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c2\<^sub>s,R\<^sub>s,G\<^sub>s) 
   since we don't get (\<sigma>,\<Sigma>)\<in>\<gamma>\<^sub>r in that case we need to prove that (c2\<^sub>c,\<sigma>) *)
lemma seq_no_ev_comp_step: assumes 
  a2:"(\<Gamma>\<^sub>c,(c1\<^sub>c, (a, b), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1\<^sub>s, (aa, bb), bc),R\<^sub>s,G\<^sub>s)" and
  a3:"(\<Gamma>\<^sub>c,c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c2\<^sub>s,R\<^sub>s,G\<^sub>s)" and a4:"Sta\<^sub>s \<gamma>\<^sub>a (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>" and
  a5:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and 
  a8:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Seq c1\<^sub>c c2\<^sub>c, CRef.toSeq ((a, b), ba)) \<rightarrow> (c\<^sub>c', CRef.toSeq ((ab, bd), ba))"
shows"\<exists>c\<^sub>s' ac be.
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq c1\<^sub>s c2\<^sub>s, CRef.toSeq ((aa, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                      (c\<^sub>s', CRef.toSeq ((ac, be), bc)) \<and>
              (((ab, bd), ba), (ac, be), bc) \<in> \<alpha> \<and>
              ((((a, b), ba), (ab, bd), ba), ((aa, bb), bc), (ac, be), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
              ((\<exists>a b bb c1\<^sub>c.
                   c\<^sub>c' = LanguageCon.com.Seq c1\<^sub>c c2\<^sub>c \<and>
                   (\<exists>c1\<^sub>s.
                       c\<^sub>s' = LanguageCon.com.Seq c1\<^sub>s c2\<^sub>s \<and>
                       ac = a \<and>
                       be = b \<and>
                       bc = bb \<and> (\<Gamma>\<^sub>c,(c1\<^sub>c, (ab, bd), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                       (\<Gamma>\<^sub>s,(c1\<^sub>s, (a, b), bb),R\<^sub>s,G\<^sub>s))) \<or>
               (\<Gamma>\<^sub>c,(c\<^sub>c', (ab, bd), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (ac, be), bc),R\<^sub>s,G\<^sub>s))"
proof(cases "c1\<^sub>c = Skip \<or> c1\<^sub>c = Throw \<or> (\<exists>f. c1\<^sub>c = Fault f) \<or> (c1\<^sub>c = Stuck)")
  let ?\<sigma> = "((a, b), ba)" and ?\<Sigma> = "((aa, bb), bc)" and ?\<sigma>' = "((ab, bd), ba)"
  case True 
  { assume a00:"c1\<^sub>c = Skip"         
    then have step_seq:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Seq c1\<^sub>c c2\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (c2\<^sub>c,toSeq ?\<sigma>)"
      using SeqSkipc by auto     
    then have alpha:"c\<^sub>c'=c2\<^sub>c \<and> toSeq ?\<sigma>' = toSeq ?\<sigma> " 
      using stepc_elim_cases1(1) a8 prod.inject stepce_stepc[OF step_seq]
      by (metis a00 stepc_elim_seq_skip(1))       
    obtain s1 s2 where  
      in_alpha:"((?\<sigma>, ?\<sigma>), ?\<Sigma>, ((s1,s2), bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c1\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeq ((s1,s2), bc)) \<and> 
                  (?\<sigma>,  ((s1,s2), bc)) \<in> \<gamma>\<^sub>r \<and> \<gamma>\<^sub>r \<subseteq> \<alpha>" 
      by (insert a2[simplified a00], erule sim_elim_cases_c(1), auto) 
    let ?\<Sigma>' = "((s1,s2), bc)"
    have sim: "(\<Gamma>\<^sub>c,(c2\<^sub>c, ?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c2\<^sub>s,  ?\<Sigma>'),R\<^sub>s,G\<^sub>s)"
      using a3 in_alpha unfolding RGSim_pre_def by auto
    have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c2\<^sub>s, toSeq ?\<Sigma>')"    
      using seq_ev_s SeqSkipc in_alpha
      by (metis (no_types, hide_lams) rtranclp.simps)   
    then have ?thesis using in_alpha sim alpha 
      unfolding toSeq_def by auto    
  }
  moreover { assume a00:"c1\<^sub>c = Throw" 
    then have step_seq:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Seq c1\<^sub>c c2\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (Throw, toSeq ?\<sigma>)"
      using SeqThrowc by auto
    then have alpha:"c\<^sub>c'=Throw \<and> toSeq ?\<sigma>' = toSeq ?\<sigma> \<and> ?\<sigma>' = ?\<sigma>"  
      using a00 Pair_inject a8 stepc_elim_seq_skip(2) throw1 fst_conv unfolding toSeq_def
      by metis
    obtain s1 s2 where in_alpha:"((?\<sigma>, ?\<sigma>), ?\<Sigma>, ((s1,s2),bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c1\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, toSeq ((s1,s2),bc))" 
           and r:"(?\<sigma>,  ((s1,s2),bc)) \<in> \<gamma>\<^sub>a" and gamm_subset:"\<gamma>\<^sub>a \<subseteq> \<alpha>"
      by (insert a2[simplified a00], erule sim_elim_cases_c(2), auto)
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, toSeq ((s1,s2),bc))" 
      using seq_ev_s SeqThrowc  
      by (metis (no_types, hide_lams) rtranclp.simps) 
    then have ?thesis using   r step_seq alpha 
      in_alpha Throw_sim[OF  gamm_subset r a4   a5] gamm_subset  a00  unfolding toSeq_def
      by fast
  }
  moreover { 
    fix f assume a00:"c1\<^sub>c = Fault f"
    then have step_seq:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Seq c1\<^sub>c c2\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (Fault f, toSeq ?\<sigma>)"
      using SeqFaultc by auto
    then have alpha:"c\<^sub>c'=Fault f \<and> toSeq ?\<sigma>' = toSeq ?\<sigma> \<and> ?\<sigma>' = ?\<sigma>"  
      using a00 Pair_inject a8 stepc_elim_seq_skip(4) Fault_ev fst_conv unfolding toSeq_def
      by metis
    obtain s1 s2 where in_alpha:" ((?\<sigma>, ?\<sigma>), ?\<Sigma>, ((s1,s2),bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c1\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq ((s1,s2),bc))" 
           and r:"(?\<sigma>,  ((s1,s2),bc)) \<in> \<alpha>" 
      by (insert a2[simplified a00], erule sim_elim_cases_c(3), auto)
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq ((s1,s2),bc))" 
      using seq_ev_s SeqFaultc  
      by (metis (no_types, hide_lams) rtranclp.simps) 
    then have ?thesis using   r step_seq alpha 
      in_alpha    a00 Fault_sim[OF r a5]  unfolding toSeq_def
      by fastforce      
  }
  moreover { 
    assume a00:"c1\<^sub>c = Stuck"
    then have step_seq:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Seq c1\<^sub>c c2\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (Stuck, toSeq ?\<sigma>)"
      using SeqStuckc by auto
    then have alpha:"c\<^sub>c'=Stuck \<and> toSeq ?\<sigma>' = toSeq ?\<sigma> \<and> ?\<sigma>' = ?\<sigma>"  
      using a00 Pair_inject a8 stepc_elim_seq_skip(3) Stuck_ev fst_conv unfolding toSeq_def
      by metis
    obtain s1 s2 where in_alpha:" ((?\<sigma>, ?\<sigma>), ?\<Sigma>, ((s1,s2),bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c1\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, toSeq ((s1,s2),bc))" 
           and r:"(?\<sigma>,  ((s1,s2),bc)) \<in> \<alpha>" 
      by (insert a2[simplified a00], erule sim_elim_cases_c(4), auto)
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, toSeq ((s1,s2),bc))" 
      using seq_ev_s SeqStuckc  
      by (metis (no_types, hide_lams) rtranclp.simps) 
    then have ?thesis using   r step_seq alpha 
      in_alpha    a00 Stuck_sim[OF r a5]  unfolding toSeq_def
      by fastforce
  }
  ultimately show ?thesis using True by fast       
next
  let ?\<sigma> = "((a, b), ba)" and ?\<Sigma> = "((aa, bb), bc)" and ?\<sigma>' = "((ab, bd), ba)"
  case False 
  then obtain c1'
    where stepc1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c1\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (c1', toSeq ?\<sigma>')" and 
          seq:    "(c\<^sub>c', toSeq ?\<sigma>')= (Seq c1' c2\<^sub>c, toSeq ?\<sigma>')"
    using  SmallStepCon.redex_not_Seq 
           stepc_elim_cases1(7)[OF a8, of "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c1\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (c1', toSeq ?\<sigma>') \<and> 
                                           (c\<^sub>c',toSeq ?\<sigma>')= (Seq c1' c2\<^sub>c,toSeq ?\<sigma>')"]
    by fastforce
  thus ?thesis 
    using  seq_ev_s stepc1 seq  
    dest_sim_tau_step[of \<Gamma>\<^sub>c c1\<^sub>c ?\<sigma> R\<^sub>c G\<^sub>c \<alpha> \<gamma>\<^sub>r \<gamma>\<^sub>a \<Gamma>\<^sub>s c1\<^sub>s ?\<Sigma> R\<^sub>s G\<^sub>s  _ ?\<sigma>', OF a2 stepc1] 
    unfolding RGSim_pre_def by fastforce    
qed

 lemma Seq_sim:  
  "\<gamma>\<^sub>a\<subseteq>\<alpha> \<Longrightarrow>
   (\<Gamma>\<^sub>c,(c1\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
   (\<Gamma>\<^sub>c,c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c2\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow> Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow>
   \<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>) \<in> G\<^sub>c \<Longrightarrow>
   (\<Gamma>\<^sub>c,(Seq c1\<^sub>c c2\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq c1\<^sub>s c2\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s)"
apply(coinduction arbitrary: \<sigma> \<Sigma> c1\<^sub>c c1\<^sub>s)
  apply clarsimp
   apply (rule conjId)+   
   apply (simp add: env_sim)
     apply (rule, rule, rule, rule, rule, fast intro: seq_ev_comp_step)      
   apply(rule, rule, rule, rule) apply(auto intro: seq_no_ev_comp_step)
   by (simp add: dest_sim_alpha)
   
    
    
 lemma Seq_sound:
  "\<gamma>\<^sub>a\<subseteq>\<alpha> \<Longrightarrow>  Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow>   \<forall>sn. (sn, sn)\<in>G\<^sub>c \<Longrightarrow> 
  (\<Gamma>\<^sub>c,c1\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>r\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c1\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow>
  (\<Gamma>\<^sub>c,c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c2\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow>
  (\<Gamma>\<^sub>c,Seq c1\<^sub>c c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,Seq c1\<^sub>s c2\<^sub>s,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def apply (auto, rule Seq_sim, auto)
  unfolding RGSim_pre_def by auto


lemma catch_no_ev_comp_step:
  assumes 
   a0:"(\<Gamma>\<^sub>c,(c1\<^sub>c, (a, b), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>) (\<Gamma>\<^sub>s,(c1\<^sub>s, (aa, bb), bc),R\<^sub>s,G\<^sub>s)" and
   a2:"(\<Gamma>\<^sub>c,c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c2\<^sub>s,R\<^sub>s,G\<^sub>s)" and   
   a4:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and
   a5:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Catch c1\<^sub>c c2\<^sub>c, CRef.toSeq ((a, b), ba)) \<rightarrow> (c\<^sub>c', CRef.toSeq ((ab, bd), ba))" and
   a6:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
   shows
       "\<exists>c\<^sub>s' ac be.
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Catch c1\<^sub>s c2\<^sub>s, CRef.toSeq ((aa, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                      (c\<^sub>s', CRef.toSeq ((ac, be), bc)) \<and>
              (((ab, bd), ba), (ac, be), bc) \<in> \<alpha> \<and>
              ((((a, b), ba), (ab, bd), ba), ((aa, bb), bc), (ac, be), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
              ((\<exists>a b bb c1\<^sub>c.
                   c\<^sub>c' = LanguageCon.com.Catch c1\<^sub>c c2\<^sub>c \<and>
                   (\<exists>c1\<^sub>s.
                       c\<^sub>s' = LanguageCon.com.Catch c1\<^sub>s c2\<^sub>s \<and>
                       ac = a \<and>
                       be = b \<and>
                       bc = bb \<and> (\<Gamma>\<^sub>c,(c1\<^sub>c, (ab, bd), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>)
                       (\<Gamma>\<^sub>s,(c1\<^sub>s, (a, b), bb),R\<^sub>s,G\<^sub>s))) \<or>
               (\<Gamma>\<^sub>c,(c\<^sub>c', (ab, bd), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (ac, be), bc),R\<^sub>s,G\<^sub>s))"
 unfolding RGSim_pre_def 
proof(cases "c1\<^sub>c = Skip \<or> c1\<^sub>c = Throw \<or> (\<exists>f. c1\<^sub>c = Fault f) \<or> (c1\<^sub>c = Stuck)")
  let ?\<sigma> = "((a, b), ba)" and ?\<Sigma> = "((aa, bb), bc)" and ?\<sigma>' = "((ab, bd), ba)"
  case True
  {assume a00:"c1\<^sub>c = Skip"         
   then have step_catch:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Catch c1\<^sub>c c2\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (Skip,toSeq ?\<sigma>)"
     using CatchSkipc by auto     
   then have alpha:"c\<^sub>c'=Skip \<and> toSeq ?\<sigma>' = toSeq ?\<sigma>" using a00
     by (metis SmallStepCon.stepc_elim_cases(1) a5 prod.inject 
         stepc_elim_cases_Catch_skip(1) stepce_stepc)         
   obtain s1 s2 where  
      in_alpha:"((?\<sigma>, ?\<sigma>), ?\<Sigma>, ((s1,s2), bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c1\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeq ((s1,s2), bc)) \<and> 
                  (?\<sigma>,  ((s1,s2), bc)) \<in> \<gamma>\<^sub>n" and \<alpha>:"\<gamma>\<^sub>n \<subseteq> \<alpha>"            
     by (insert a0[simplified a00], erule sim_elim_cases_c(1), auto)
   let ?\<Sigma>' = "((s1,s2), bc)"   
   have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Catch c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeq ?\<Sigma>')"    
     using catch_ev_s CatchSkipc in_alpha
     by (metis (no_types, hide_lams) rtranclp.simps) 
   then have ?thesis using in_alpha alpha[simplified  toSeq.simps] Skip_sound[OF \<alpha> a6 a4] \<alpha>
      unfolding toSeq_def RGSim_pre_def by(auto, blast)               
  } 
  moreover { 
    assume a00:"c1\<^sub>c = Throw" 
    then have a00:"c1\<^sub>c = Throw" by auto
    then have step_seq:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Catch c1\<^sub>c c2\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (c2\<^sub>c,toSeq ?\<sigma>)"
      using CatchThrowc by auto 
    then have alpha:"c\<^sub>c'=c2\<^sub>c \<and> toSeq ?\<sigma>' = toSeq ?\<sigma>" using a00
               a5 fst_conv                
      by (metis snd_conv stepc_elim_seq_skip(6) throw1)
    obtain s1 s2 where in_alpha:"((?\<sigma>, ?\<sigma>), ?\<Sigma>,((s1,s2), bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c1\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, toSeq ((s1,s2), bc))" 
         and r:"(?\<sigma>, ((s1,s2), bc)) \<in> \<gamma>\<^sub>r"  and \<alpha>:"\<gamma>\<^sub>r \<subseteq> \<alpha>"       
      by (insert a0[simplified a00], erule sim_elim_cases_c(2), auto)        
    let ?\<Sigma>' = "((s1,s2), bc)"
    have sim: "(\<Gamma>\<^sub>c,(c2\<^sub>c, ?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c2\<^sub>s, ?\<Sigma>'),R\<^sub>s,G\<^sub>s)"
      using a2 in_alpha a00 r unfolding RGSim_pre_def by auto
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Catch c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c2\<^sub>s, toSeq ?\<Sigma>')"       
      by (meson catch_ev_s in_alpha rtranclp.rtrancl_into_rtrancl stepce.CatchThrowc)
    then have ?thesis using a00 alpha in_alpha alpha sim r \<alpha> unfolding toSeq_def by auto 
  }
  moreover { 
    fix f assume a00:"c1\<^sub>c = Fault f"
    then have step_seq:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Catch c1\<^sub>c c2\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (Fault f, toSeq ?\<sigma>)"
      using CatchFaultc by auto
    then have alpha:"c\<^sub>c'=Fault f \<and> toSeq ?\<sigma>' = toSeq ?\<sigma> \<and> ?\<sigma>' = ?\<sigma>"  
      using a00 Pair_inject a5 stepc_elim_seq_skip(8) Fault_ev fst_conv unfolding toSeq_def
      by metis
    obtain s1 s2 where in_alpha:" ((?\<sigma>, ?\<sigma>), ?\<Sigma>, ((s1,s2),bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c1\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq ((s1,s2),bc))" 
           and r:"(?\<sigma>,  ((s1,s2),bc)) \<in> \<alpha>" 
      by (insert a0[simplified a00], erule sim_elim_cases_c(3), auto)
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Catch c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq ((s1,s2),bc))" 
      using catch_ev_s CatchFaultc  
      by (metis (no_types, hide_lams) rtranclp.simps) 
    then have ?thesis using   r step_seq alpha 
      in_alpha    a00 Fault_sim[OF r a4]  unfolding toSeq_def
      by fastforce    
  }
  moreover { 
    assume a00:"c1\<^sub>c = Stuck"
    then have step_seq:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Catch c1\<^sub>c c2\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (Stuck, toSeq ?\<sigma>)"
      using CatchStuckc by auto
    then have alpha:"c\<^sub>c'=Stuck \<and> toSeq ?\<sigma>' = toSeq ?\<sigma> \<and> ?\<sigma>' = ?\<sigma>"  
      using a00 Pair_inject a5 stepc_elim_seq_skip(7) Stuck_ev fst_conv unfolding toSeq_def
      by metis
    obtain s1 s2 where in_alpha:" ((?\<sigma>, ?\<sigma>), ?\<Sigma>, ((s1,s2),bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c1\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, toSeq ((s1,s2),bc))" 
           and r:"(?\<sigma>,  ((s1,s2),bc)) \<in> \<alpha>" 
      by (insert a0[simplified a00], erule sim_elim_cases_c(4), auto)
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Catch c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, toSeq ((s1,s2),bc))" 
      using catch_ev_s CatchStuckc  
      by (metis (no_types, hide_lams) rtranclp.simps) 
    then have ?thesis using   r step_seq alpha 
      in_alpha    a00 Stuck_sim[OF r a4]  unfolding toSeq_def
      by fastforce 
  }
  ultimately show ?thesis using  True by auto       
next
  let ?\<sigma> = "((a, b), ba)" and ?\<Sigma> = "((aa, bb), bc)" and ?\<sigma>' = "((ab, bd), ba)"
  case False 
  then obtain c1'
    where stepc1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c1\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (c1', toSeq ?\<sigma>')" and 
          catch:    "(c\<^sub>c', toSeq ?\<sigma>')= (Catch c1' c2\<^sub>c, toSeq ?\<sigma>')"
    using  SmallStepCon.redex_not_Catch 
           stepc_elim_cases1(14)[OF a5, of "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c1\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (c1', toSeq ?\<sigma>') \<and> 
                                            (c\<^sub>c', toSeq ?\<sigma>')= (Catch c1' c2\<^sub>c,toSeq ?\<sigma>')"]
    by fastforce 
  thus ?thesis 
    using  catch_ev_s stepc1 catch  
    dest_sim_tau_step[of \<Gamma>\<^sub>c c1\<^sub>c ?\<sigma> R\<^sub>c G\<^sub>c \<alpha> \<gamma>\<^sub>n \<gamma>\<^sub>r \<Gamma>\<^sub>s c1\<^sub>s ?\<Sigma> R\<^sub>s G\<^sub>s  _ ?\<sigma>', OF a0 stepc1] 
    unfolding RGSim_pre_def by fastforce
qed  
    
lemma catch_ev_comp_step:
  assumes a0:"(\<Gamma>\<^sub>c,(c1\<^sub>c, (a, b), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>) (\<Gamma>\<^sub>s,(c1\<^sub>s, (aa, bb), bc),R\<^sub>s,G\<^sub>s)" and
        a1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Catch c1\<^sub>c c2\<^sub>c, toSeq ((a, b), ba)) \<rightarrow> (c\<^sub>c', toSeq ((ab, bd), ba))"
      shows "\<exists>c\<^sub>s' ac be.
              (\<exists>a ab b.
                  \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Catch c1\<^sub>s c2\<^sub>s, toSeq ((aa, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                  (\<exists>aa ad ba.
                      \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, ab, b) \<rightarrow> (aa, ad, ba) \<and>
                      \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ad, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((ac, be), bc)))) \<and>
              (((ab, bd), ba), (ac, be), bc) \<in> \<alpha> \<and>
              ((((a, b), ba), (ab, bd), ba), ((aa, bb), bc), (ac, be), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
              ((\<exists>a b bb c1\<^sub>c.
                   c\<^sub>c' = Catch c1\<^sub>c c2\<^sub>c \<and>
                   (\<exists>c1\<^sub>s.
                       c\<^sub>s' = Catch c1\<^sub>s c2\<^sub>s \<and>
                       ac = a \<and>
                       be = b \<and>
                       bc = bb \<and> (\<Gamma>\<^sub>c,(c1\<^sub>c, (ab, bd), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>)
                       (\<Gamma>\<^sub>s,(c1\<^sub>s, (a, b), bb),R\<^sub>s,G\<^sub>s))) \<or>
               (\<Gamma>\<^sub>c,(c\<^sub>c', (ab, bd), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (ac, be), bc),R\<^sub>s,G\<^sub>s))"  
proof-
  have "c1\<^sub>c\<noteq>Skip \<and> c1\<^sub>c\<noteq>Throw" 
    using not_catch_skip_throw_ev a1 by fastforce
  then obtain c1'
     where stepc1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (c1\<^sub>c, toSeq ((a, b), ba)) \<rightarrow> (c1', toSeq ((ab, bd), ba))" and 
          catch:    "(c\<^sub>c', ((ab, bd), ba))= (Catch c1' c2\<^sub>c,  ((ab, bd), ba))" 
    using stepc_elim_cases1(14)[OF a1, of "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (c1\<^sub>c, toSeq ((a, b), ba)) \<rightarrow> 
                                                      (c1', toSeq ((ab, bd), ba)) \<and> 
                                          (c\<^sub>c', toSeq ((ab, bd), ba))= 
                                          (Catch c1' c2\<^sub>c, toSeq ((ab, bd), ba))"]
    by fastforce
  thus ?thesis 
    using  catch_ev_plus stepc1 catch a0
    dest_sim_ev_step[OF a0 stepc1] 
    by fastforce
qed     
  
 lemma Catch_sim:  
  "(\<Gamma>\<^sub>c,(c1\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>) (\<Gamma>\<^sub>s,(c1\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>
   (\<Gamma>\<^sub>c,c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c2\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow> Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow>   
   \<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c \<Longrightarrow>
   (\<Gamma>\<^sub>c,(Catch c1\<^sub>c c2\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
   (\<Gamma>\<^sub>s,(Catch c1\<^sub>s c2\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s)"
apply(coinduction arbitrary: \<sigma> \<Sigma> c1\<^sub>c c1\<^sub>s)
  apply clarsimp
   apply (rule conjId)+    
   apply (simp add: env_sim)
   apply (rule, rule, rule, rule, rule) apply(fast intro: catch_ev_comp_step)      
   apply(rule, rule, rule, rule) apply(auto intro: catch_no_ev_comp_step)
  by (simp add: dest_sim_alpha)
    
lemma Catch_sound:
  "\<xi> \<subseteq> \<alpha> \<Longrightarrow> Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow>  \<forall>sn. (sn, sn)\<in>G\<^sub>c \<Longrightarrow> 
  (\<Gamma>\<^sub>c,c1\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>) (\<Gamma>\<^sub>s,c1\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow>
  (\<Gamma>\<^sub>c,c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>r\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c2\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow> Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow> 
  (\<Gamma>\<^sub>c,Catch c1\<^sub>c c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,Catch c1\<^sub>s c2\<^sub>s,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def apply (auto, rule Catch_sim, auto)
  unfolding RGSim_pre_def by auto
    
lemma env:
  assumes 
    a1: "(\<sigma>n, \<Sigma>n) \<in> \<xi>" and
    a2: "Sta\<^sub>s \<xi> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>" and  
    a3:"(((\<sigma>n, \<sigma>'), \<Sigma>n, \<Sigma>') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
  shows"(\<sigma>', \<Sigma>') \<in> \<xi> \<or>
        (\<Gamma>\<^sub>c,(c\<^sub>c, \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,\<Sigma>'),R\<^sub>s,G\<^sub>s) "
  using sim_env[OF a1 a2 a3] by fastforce
 
 
lemma If_sim:
  assumes 
  a1:"\<xi> \<subseteq> \<alpha>" and 
  a2:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and 
  a3:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and  
  a5:" \<xi> \<subseteq> \<up>((b\<^sub>c \<rightleftharpoons> b\<^sub>s))" and a6:"\<xi>\<^sub>1 = \<xi> \<inter> \<up>(b\<^sub>c \<odot> b\<^sub>s)" and 
  a7:"\<xi>\<^sub>2 = \<xi> \<inter> \<up>((-b\<^sub>c) \<odot> (-b\<^sub>s) )" and  
  a8:"(\<sigma>,\<Sigma>)\<in>\<xi>" and
  a9:"(\<Gamma>\<^sub>c,c1\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c1\<^sub>s,R\<^sub>s,G\<^sub>s)" and 
  a10:"(\<Gamma>\<^sub>c,c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>2\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c2\<^sub>s,R\<^sub>s,G\<^sub>s)"
shows  
  "(\<Gamma>\<^sub>c,(Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Cond b\<^sub>s c1\<^sub>s c2\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s)"
using  a1 a2 a3  a5 a6 a7  a8 a9 a10
  apply(coinduction arbitrary: \<sigma> \<Sigma>)   
proof(clarsimp)
  fix a b ba aa bb bc
  let ?\<sigma> = "((a::'a,b::'b),ba::'b list)" and ?\<Sigma> = "((aa::'c,bb::'d),bc::'d list)"
    assume 
       a0:"(?\<sigma>, ?\<Sigma>) \<in> \<xi>" and              
       a3:"Sta\<^sub>s \<xi> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>" and                            
       a8:"\<xi> \<subseteq> \<alpha>" and                     
       a13:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c"     
    have \<alpha>:"(?\<sigma>, ?\<Sigma>) \<in> \<alpha>" using a0 a8 by fastforce 
    moreover have "\<forall>\<sigma>' \<Sigma>'.
           (((?\<sigma>, \<sigma>'), ?\<Sigma>, \<Sigma>') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>)  \<longrightarrow>
           (\<sigma>', \<Sigma>') \<in> \<xi> \<or>
           (\<Gamma>\<^sub>c,(Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
           (\<Gamma>\<^sub>s,(Cond b\<^sub>s c1\<^sub>s c2\<^sub>s, \<Sigma>'),R\<^sub>s,G\<^sub>s)" 
      using env[OF a0 a3 ] by blast
    moreover have "\<forall>v c\<^sub>c' \<sigma>'.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (c\<^sub>c', toSeq \<sigma>')  \<and> ba = snd \<sigma>' \<longrightarrow>
           (\<exists>c\<^sub>s' \<Sigma>'.
               (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Cond b\<^sub>s c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                      (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq \<Sigma>'))) \<and>
               (\<sigma>', \<Sigma>') \<in> \<alpha> \<and> bc = snd \<Sigma>' \<and>
               (((?\<sigma>, \<sigma>'), ?\<Sigma>,  \<Sigma>') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (c\<^sub>c' = Cond b\<^sub>c c1\<^sub>c c2\<^sub>c \<and>
                c\<^sub>s' = Cond b\<^sub>s c1\<^sub>s c2\<^sub>s \<and> (\<sigma>', \<Sigma>') \<in> \<xi> \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)))"
      by (meson option.discI stepc_elim_cases2(1))
    moreover have "\<forall>c\<^sub>c' \<sigma>'.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (c\<^sub>c', toSeq \<sigma>') \<and> ba = snd \<sigma>' \<longrightarrow>
           (\<exists>c\<^sub>s' \<Sigma>'.
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Cond b\<^sub>s c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq \<Sigma>') \<and>
               (\<sigma>', \<Sigma>') \<in> \<alpha> \<and> bc = snd \<Sigma>' \<and>
               (((?\<sigma>, \<sigma>'), ?\<Sigma>, \<Sigma>') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (c\<^sub>c' = Cond b\<^sub>c c1\<^sub>c c2\<^sub>c \<and>
                c\<^sub>s' = Cond b\<^sub>s c1\<^sub>s c2\<^sub>s \<and> (\<sigma>', \<Sigma>') \<in> \<xi> \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s)))"
    proof -
    { fix c\<^sub>c' \<sigma>'
      assume  a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (c\<^sub>c',  toSeq \<sigma>')" and a01:"ba = snd \<sigma>'"
      then have eqs:"?\<sigma> = \<sigma>'"
        using stepc_elim_cases2(1) unfolding toSeq_def
        by (metis prod.exhaust_sel snd_conv) 
      have guar:"((?\<sigma>, ?\<sigma>), ?\<Sigma>, ?\<Sigma>) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
        using  a13 a0 a8  unfolding related_transitions_def Id_def by blast
      have h:"(c\<^sub>c'=c1\<^sub>c \<and> toSeq \<sigma>'\<in>b\<^sub>c) \<or> (c\<^sub>c'=c2\<^sub>c \<and> toSeq \<sigma>'\<in> -b\<^sub>c)"  
        using stepc_elim_cases2(1)[OF a00] eqs unfolding toSeq_def by auto        
      {
        assume c:"c\<^sub>c' = c1\<^sub>c \<and> toSeq \<sigma>' \<in> b\<^sub>c"
        then have sig1:"(\<sigma>',  ?\<Sigma>) \<in> \<xi>\<^sub>1"
          using a0 a5 a6 a7 eqs unfolding eq_rel_def and_rel_def ext_set_def toSeq_def by auto
        then have sn_inb:"toSeq ?\<Sigma> \<in> b\<^sub>s" 
          using a6 unfolding and_rel_def toSeq_def ext_set_def by auto
        then have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Cond b\<^sub>s c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c1\<^sub>s, toSeq ?\<Sigma>)"          
          by (simp add: sn_inb r_into_rtranclp stepce.CondTruec)        
        have x:"(\<Gamma>\<^sub>c,(c1\<^sub>c, \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1\<^sub>s,  ?\<Sigma>),R\<^sub>s,G\<^sub>s)" 
          using a9  sig1
          unfolding RGSim_pre_def
        by blast
        note l = conjI[OF x steps]
      }         
      moreover {
        assume c:"c\<^sub>c' = c2\<^sub>c \<and> toSeq \<sigma>' \<in> -b\<^sub>c"
        then have sig1:"(\<sigma>', ?\<Sigma>) \<in> \<xi>\<^sub>2"
          using a0 a5 a6 a7 eqs unfolding eq_rel_def  and_rel_def ext_set_def toSeq_def by auto
        then have sn_inb:"toSeq ?\<Sigma>\<in>-b\<^sub>s" using a7 unfolding and_rel_def toSeq_def ext_set_def by auto
        then have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Cond b\<^sub>s c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c2\<^sub>s, toSeq ?\<Sigma>)"          
          by (simp add: sn_inb r_into_rtranclp stepce.CondFalsec)        
        have x:"(\<Gamma>\<^sub>c,(c2\<^sub>c, \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c2\<^sub>s, ?\<Sigma>),R\<^sub>s,G\<^sub>s)" 
          using a10  sig1
          unfolding RGSim_pre_def by blast
        note l = conjI[OF x steps]
      } 
      ultimately have "\<exists>c\<^sub>s' \<Sigma>'.
             \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Cond b\<^sub>s c1\<^sub>s c2\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq \<Sigma>') \<and> snd ?\<Sigma> = snd \<Sigma>' \<and>
             (\<sigma>', \<Sigma>') \<in> \<alpha> \<and>
             (((?\<sigma>, \<sigma>'), ?\<Sigma>, \<Sigma>') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (c\<^sub>c' = Cond b\<^sub>c c1\<^sub>c c2\<^sub>c \<and>
              c\<^sub>s' = Cond b\<^sub>s c1\<^sub>s c2\<^sub>s \<and> (\<sigma>', \<Sigma>') \<in> \<xi> \<or>
              (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', \<Sigma>'),R\<^sub>s,G\<^sub>s))" 
        using guar  h  eqs \<alpha> by auto   
     } then show ?thesis by auto
   qed     
   ultimately show 
    "(((a, b), ba), (aa, bb), bc) \<in> \<alpha> \<and>
           (\<forall>c\<^sub>c' ab bd.
               \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, CRef.toSeq ((a, b), ba)) \<rightarrow>
                        (c\<^sub>c', CRef.toSeq ((ab, bd), ba)) \<longrightarrow>
               (\<exists>c\<^sub>s' ac be.
                   \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Cond b\<^sub>s c1\<^sub>s c2\<^sub>s, CRef.toSeq ((aa, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                           (c\<^sub>s', CRef.toSeq ((ac, be), bc)) \<and>
                   (((ab, bd), ba), (ac, be), bc) \<in> \<alpha> \<and>
                   ((((a, b), ba), (ab, bd), ba), ((aa, bb), bc), (ac, be), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                   (c\<^sub>c' = LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c \<and>
                    c\<^sub>s' = LanguageCon.com.Cond b\<^sub>s c1\<^sub>s c2\<^sub>s \<and> (((ab, bd), ba), (ac, be), bc) \<in> \<xi> \<or>
                    (\<Gamma>\<^sub>c,(c\<^sub>c', (ab, bd), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                    (\<Gamma>\<^sub>s,(c\<^sub>s', (ac, be), bc),R\<^sub>s,G\<^sub>s)))) \<and>
           (\<forall>v c\<^sub>c' ab bd.
               \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>Some v (LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, CRef.toSeq ((a, b), ba)) \<rightarrow>
                              (c\<^sub>c', CRef.toSeq ((ab, bd), ba)) \<longrightarrow>
               (\<exists>c\<^sub>s' ac be.
                   (\<exists>a ab b.
                       \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Cond b\<^sub>s c1\<^sub>s c2\<^sub>s, CRef.toSeq ((aa, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                               (a, ab, b) \<and>
                       (\<exists>aa ad ba.
                           \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, ab, b) \<rightarrow> (aa, ad, ba) \<and>
                           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ad, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', CRef.toSeq ((ac, be), bc)))) \<and>
                   (((ab, bd), ba), (ac, be), bc) \<in> \<alpha> \<and>
                   ((((a, b), ba), (ab, bd), ba), ((aa, bb), bc), (ac, be), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                   (c\<^sub>c' = LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c \<and>
                    c\<^sub>s' = LanguageCon.com.Cond b\<^sub>s c1\<^sub>s c2\<^sub>s \<and> (((ab, bd), ba), (ac, be), bc) \<in> \<xi> \<or>
                    (\<Gamma>\<^sub>c,(c\<^sub>c', (ab, bd), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                    (\<Gamma>\<^sub>s,(c\<^sub>s', (ac, be), bc),R\<^sub>s,G\<^sub>s)))) \<and>
           (\<forall>ab bd be ac bf bg.
               ((((a, b), ba), (ab, bd), be), ((aa, bb), bc), (ac, bf), bg) \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<longrightarrow>
               (((ab, bd), be), (ac, bf), bg) \<in> \<xi> \<or>
               (\<Gamma>\<^sub>c,(LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, (ab, bd), be),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
               (\<Gamma>\<^sub>s,(LanguageCon.com.Cond b\<^sub>s c1\<^sub>s c2\<^sub>s, (ac, bf), bg),R\<^sub>s,G\<^sub>s))" 
      by auto
  qed    


 
lemma If_sound:
  "\<xi> \<subseteq> \<alpha>  \<Longrightarrow> Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow> 
  \<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c  \<Longrightarrow>
   \<xi> \<subseteq> \<up>(b\<^sub>c \<rightleftharpoons> b\<^sub>s) \<Longrightarrow> \<xi>\<^sub>1= \<xi> \<inter> \<up>(b\<^sub>c \<odot> b\<^sub>s) \<Longrightarrow> \<xi>\<^sub>2= \<xi> \<inter> \<up>((-b\<^sub>c) \<odot> (-b\<^sub>s) ) \<Longrightarrow>
  (\<Gamma>\<^sub>c,c1\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c1\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow> 
  (\<Gamma>\<^sub>c,c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>2\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c2\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow> 
  (\<Gamma>\<^sub>c,Cond b\<^sub>c c1\<^sub>c c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,Cond b\<^sub>s c1\<^sub>s c2\<^sub>s,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def apply (auto,rule If_sim, auto)
  unfolding RGSim_pre_def by auto+

definition coPre 
where 
"coPre \<xi> b\<^sub>c b\<^sub>s \<Gamma>\<^sub>c c1\<^sub>c R\<^sub>c G\<^sub>c \<alpha> \<gamma>\<^sub>n \<gamma>\<^sub>a \<Gamma>\<^sub>s c1\<^sub>s R\<^sub>s G\<^sub>s \<Gamma>\<^sub>c' csc R\<^sub>c' G\<^sub>c' \<alpha>' \<gamma>\<^sub>n' \<gamma>\<^sub>a' \<Gamma>\<^sub>s' css R\<^sub>s' G\<^sub>s' \<equiv>
 \<exists>\<sigma> \<Sigma> c\<^sub>c c\<^sub>s.
   \<Gamma>\<^sub>c' = \<Gamma>\<^sub>c \<and>
   ( (csc = (Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c),  \<sigma>) \<and> 
      css = (Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s),  \<Sigma>) \<and>      
     (\<Gamma>\<^sub>c,(c\<^sub>c,  \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,  \<Sigma>),R\<^sub>s,G\<^sub>s)) \<or>     
    ((csc = (While b\<^sub>c c1\<^sub>c, \<sigma>) \<and> 
     css = (While b\<^sub>s c1\<^sub>s, \<Sigma>) \<and> (\<sigma>,\<Sigma>) \<in>\<xi>)) \<or>
    (csc = (Skip, \<sigma>) \<and> 
     css = (Skip, \<Sigma>) \<and> (\<sigma>,\<Sigma>) \<in> \<xi> \<and> (fst \<sigma>)\<in> (- b\<^sub>c))  \<or>
    (csc = (Throw, \<sigma>) \<and> 
     css = (Throw, \<Sigma>) \<and> (\<sigma>,\<Sigma>) \<in>\<gamma>\<^sub>a ) \<or> 
    (\<exists>f. csc = (Fault f, \<sigma>) \<and> css = (Fault f, \<Sigma>) \<and> (\<sigma>,\<Sigma>) \<in> \<alpha> ) \<or> 
    (csc = (Stuck, \<sigma>) \<and> css = (Stuck,\<Sigma>) \<and> (\<sigma>,\<Sigma>) \<in> \<alpha>)  ) \<and>
   R\<^sub>c' = R\<^sub>c \<and> G\<^sub>c' = G\<^sub>c \<and> \<alpha>' = \<alpha> \<and> \<gamma>\<^sub>n' = \<gamma>\<^sub>n \<and> \<gamma>\<^sub>a' = \<gamma>\<^sub>a \<and> \<Gamma>\<^sub>s' = \<Gamma>\<^sub>s \<and> R\<^sub>s' = R\<^sub>s \<and> G\<^sub>s' = G\<^sub>s "


lemma while_seq_alpha:
  "  \<xi> \<subseteq> \<alpha> \<Longrightarrow> \<gamma>\<^sub>a \<subseteq> \<alpha> \<Longrightarrow> 
    (\<exists>c\<^sub>c. a = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
               aa = ad \<and> b = bd \<and> ba = be \<and>
               (\<exists>c\<^sub>s. ab = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> 
               (\<Gamma>\<^sub>c,(c\<^sub>c, (ad, bd), be),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ae, bf), bg),R\<^sub>s,G\<^sub>s))) \<or>
        a =While b\<^sub>c c1\<^sub>c \<and> aa = ad \<and> b = bd \<and> ba = be \<and> 
          ab = While b\<^sub>s c1\<^sub>s \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<or>
        a = Skip \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Skip \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> 
          (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<and> (ad, bd) \<notin> b\<^sub>c \<or>
        a = Throw \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Throw \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> 
          (((ad, bd), be), (ae, bf), bg) \<in> \<gamma>\<^sub>a \<or>
        (\<exists>f. a = Fault f \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Fault f \<and> 
             ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>) \<or>
        a = Stuck \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Stuck \<and> 
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha> \<Longrightarrow> 
 (((aa, b), ba), (ac, bb), bc) \<in> \<alpha> "  
  by (auto dest: dest_sim_alpha)

lemma while_seq_no_ev1:
  assumes 
  a0:"(\<exists>c\<^sub>c. a = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
               (\<exists>c\<^sub>s. ab = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and>
               (\<Gamma>\<^sub>c,(c\<^sub>c, (aa, b), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ac, bb), bc),R\<^sub>s,G\<^sub>s)))" and
  a1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (a, toSeq ((aa, b), ba)) \<rightarrow> (c\<^sub>c', CRef.toSeq ((af, bh), ba))"
  shows "\<exists>c\<^sub>s' a bd.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((a, bd), bc)) \<and>
          (((af, bh), ba), (a, bd), bc) \<in> \<alpha> \<and>
          (((((aa, b), ba), (af, bh), ba), ((ac, bb), bc), (a, bd), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          ((\<exists>aa b bb ab be bf.
               (\<exists>c\<^sub>c. c\<^sub>c' = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
                      af = aa \<and> bh = b \<and> ba = bb \<and>
                      (\<exists>c\<^sub>s. c\<^sub>s' = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                      (\<Gamma>\<^sub>c,(c\<^sub>c, (aa, b), bb),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ab, be), bf),R\<^sub>s,G\<^sub>s))) \<or>
               c\<^sub>c' = While b\<^sub>c c1\<^sub>c \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                 c\<^sub>s' = While b\<^sub>s c1\<^sub>s \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<or>
               c\<^sub>c' = Skip \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Skip \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<and> (aa, b) \<notin> b\<^sub>c \<or>
               c\<^sub>c' = Throw \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Throw \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<gamma>\<^sub>a \<or>
               (\<exists>f. c\<^sub>c' = Fault f \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                    c\<^sub>s' = Fault f \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                   (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
               c\<^sub>c' = Stuck \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Stuck \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', (af, bh), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (a, bd), bc),R\<^sub>s,G\<^sub>s))" 
proof -
  let ?\<sigma> = "((aa, b), ba)" and ?\<Sigma> = "((ac, bb), bc)" and ?\<sigma>' = "((af, bh), ba)"
  obtain c\<^sub>c c\<^sub>s where 
    a0:"a = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c)  \<and> 
         ab = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and>
         (\<Gamma>\<^sub>c,(c\<^sub>c, ?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, ?\<Sigma>),R\<^sub>s,G\<^sub>s)" 
    using a0 by auto
  then have a14a:"Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) = a" and
            a14c:"ab = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s)"  and
            a14e:"(\<Gamma>\<^sub>c,(c\<^sub>c, ?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, ?\<Sigma>),R\<^sub>s,G\<^sub>s)" and 
            a15:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c), toSeq ?\<sigma>) \<rightarrow> (c\<^sub>c', toSeq ?\<sigma>')" using a1 by auto
  thus ?thesis 
  proof (cases "c\<^sub>c = Skip \<or> c\<^sub>c = Throw \<or> (\<exists>f. c\<^sub>c = Fault f) \<or>  c\<^sub>c = Stuck")
    case True
    {assume a00:"c\<^sub>c = Skip"
      then have step_seq:
        "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c), toSeq ?\<sigma>) \<rightarrow> ((While b\<^sub>c c1\<^sub>c), toSeq ?\<sigma>)"
        using SeqSkipc by auto
      then have alpha:"c\<^sub>c'= (While b\<^sub>c c1\<^sub>c) \<and> ?\<sigma>' = ?\<sigma>" using a00 a0  a1 unfolding toSeq_def
        by (metis fst_conv snd_conv stepc_elim_cases1(1) stepc_elim_seq_skip(1))         
      have ?thesis 
      proof -        
       obtain a1 a2  where 
           in_alpha:"((?\<sigma>, ?\<sigma>), ?\<Sigma>, ((a1,a2),bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
                     \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeq ((a1,a2),bc)) \<and> bc = snd ((a1,a2),bc) \<and> 
                     (?\<sigma>, ((a1,a2),bc)) \<in> \<xi>"       
         using sim_elim_cases_c(1)[OF a14e[simplified a00]] snd_conv apply auto
         by metis
         then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s), toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* ((While b\<^sub>s c1\<^sub>s), toSeq((a1,a2),bc) )"    
           using seq_ev_s SeqSkipc in_alpha
           by (metis (no_types, hide_lams) rtranclp.simps)          
         then show ?thesis using in_alpha  alpha  a14c  
           unfolding related_transitions_def toSeq_def by blast        
      qed        
    } note l1=this  
    moreover {
      assume a00:"c\<^sub>c = Throw"      
      then have step_seq:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c),toSeq ?\<sigma>) \<rightarrow> (Throw, toSeq ?\<sigma>)"
        using SeqThrowc by auto          
      then have alpha:"c\<^sub>c'=Throw \<and> ?\<sigma>' = ?\<sigma>" 
        using a00 a0 a15  
               stepc_elim_cases1(7)[OF a15, of "c\<^sub>c'=Throw \<and> ?\<sigma>' = ?\<sigma>"] a00
        unfolding toSeq_def 
        by (auto dest:stepc_elim_cases1(13))                 
      then obtain s1 s2 where in_alpha:"((?\<sigma>, ?\<sigma>), ?\<Sigma>, ((s1,s2),bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, toSeq ((s1,s2),bc)) " and 
         r:"(?\<sigma>, ((s1,s2),bc)) \<in> \<gamma>\<^sub>a"               
        using a00 a0 sim_elim_cases_c(2)[OF a14e[simplified a00]] snd_conv apply auto
         by metis
      then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s),toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, toSeq ((s1,s2),bc))"         
        using seq_ev_s SeqThrowc            
        by (metis (no_types, hide_lams) rtranclp.simps)           
      then have ?thesis
        using a14c alpha in_alpha r unfolding related_transitions_def toSeq_def by blast           
    }
    moreover {
      assume a00:"c\<^sub>c = Stuck"      
      then have step_seq:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c),toSeq ?\<sigma>) \<rightarrow> (Stuck, toSeq ?\<sigma>)"
        using SeqStuckc by auto          
      then have alpha:"c\<^sub>c'=Stuck \<and> ?\<sigma>' = ?\<sigma>" 
        using a00 a0 a15  
               stepc_elim_cases1(7)[OF a15, of "c\<^sub>c'=Stuck \<and> ?\<sigma>' = ?\<sigma>"] a00
        unfolding toSeq_def 
        by (auto dest:stepc_elim_cases1(3))                 
      then obtain s1 s2 where in_alpha:"((?\<sigma>, ?\<sigma>), ?\<Sigma>, ((s1,s2),bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, toSeq ((s1,s2),bc)) " and 
         r:"(?\<sigma>, ((s1,s2),bc)) \<in> \<alpha>"               
        using a00 a0 sim_elim_cases_c(4)[OF a14e[simplified a00]] snd_conv apply auto
         by metis
      then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s),toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, toSeq ((s1,s2),bc))"         
        using seq_ev_s SeqStuckc            
        by (metis (no_types, hide_lams) rtranclp.simps)           
      then have ?thesis
        using a14c alpha in_alpha r unfolding related_transitions_def toSeq_def by auto           
    }
    moreover { fix f
      assume a00:"c\<^sub>c = Fault f"      
      then have step_seq:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c),toSeq ?\<sigma>) \<rightarrow> (Fault f, toSeq ?\<sigma>)"
        using SeqFaultc by auto          
      then have alpha:"c\<^sub>c'=Fault f \<and> ?\<sigma>' = ?\<sigma>" 
        using a00 a0 a15  
               stepc_elim_cases1(7)[OF a15, of "c\<^sub>c'=Fault f \<and> ?\<sigma>' = ?\<sigma>"] a00
        unfolding toSeq_def 
        by (auto dest:stepc_elim_cases1(2))                 
      then obtain s1 s2 where in_alpha:"((?\<sigma>, ?\<sigma>), ?\<Sigma>, ((s1,s2),bc)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq ((s1,s2),bc)) " and 
         r:"(?\<sigma>, ((s1,s2),bc)) \<in> \<alpha>"               
        using a00 a0 sim_elim_cases_c(3)[OF a14e[simplified a00]] snd_conv apply auto
         by metis
      then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s),toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq ((s1,s2),bc))"         
        using seq_ev_s SeqFaultc            
        by (metis (no_types, hide_lams) rtranclp.simps)           
      then have ?thesis
        using a14c alpha in_alpha r unfolding related_transitions_def toSeq_def by auto           
    }
    ultimately show ?thesis using l1 True by fastforce
  next
    case False       
    then obtain c\<^sub>c1' 
    where stepc1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (c\<^sub>c1', toSeq ?\<sigma>')" and 
          seq:    "(c\<^sub>c', toSeq ?\<sigma>')= (Seq c\<^sub>c1' (While b\<^sub>c c1\<^sub>c), toSeq ?\<sigma>')"
    using  SmallStepCon.redex_not_Seq 
           stepc_elim_cases1(7)[OF a15, 
             of "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (c\<^sub>c1', toSeq ?\<sigma>') \<and> (c\<^sub>c', ?\<sigma>')= (Seq c\<^sub>c1' (While b\<^sub>c c1\<^sub>c), ?\<sigma>')"]
    by fastforce
  thus ?thesis 
    using  seq_ev_s stepc1 seq a0 
    dest_sim_tau_step[of \<Gamma>\<^sub>c c\<^sub>c ?\<sigma> R\<^sub>c G\<^sub>c \<alpha> \<xi> \<gamma>\<^sub>a \<Gamma>\<^sub>s c\<^sub>s ?\<Sigma> R\<^sub>s G\<^sub>s  _ ?\<sigma>', OF a14e stepc1] 
    unfolding RGSim_pre_def toSeq_def by fastforce      
  qed        
qed    

lemma while_seq_no_ev2:
  assumes 
  a0:"(\<Gamma>\<^sub>c,c1\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c1\<^sub>s,R\<^sub>s,G\<^sub>s)" and    
  a3:"\<xi> \<subseteq> \<alpha>" and a4:" aa = ad \<and> b = bd \<and> ba = be \<and> ac = ae \<and> bb = bf \<and> bc = bg" and 
  a9:"\<xi> \<subseteq> \<up>(b\<^sub>c \<rightleftharpoons> b\<^sub>s)" and
  a10:"\<xi>\<^sub>1 = \<xi> \<inter> \<up>(b\<^sub>c \<odot>  b\<^sub>s)" and
  a13:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and
  a14:"(((aa, b), ba), (ac, bb), bc) \<in> \<xi>" and
  a15:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (While b\<^sub>c c1\<^sub>c,toSeq ((aa, b), ba)) \<rightarrow> (c\<^sub>c', toSeq ((af, bh), ba))"
shows "\<exists>c\<^sub>s' a bd.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.While b\<^sub>s c1\<^sub>s , toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((a, bd), bc)) \<and>
          (((af, bh), ba), (a, bd), bc) \<in> \<alpha> \<and>
          (((((aa, b), ba), (af, bh), ba), ((ac, bb), bc), (a, bd), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          ((\<exists>aa b bb ab be bf.
               (\<exists>c\<^sub>c. c\<^sub>c' = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
                      af = aa \<and> bh = b \<and> ba = bb \<and>
                      (\<exists>c\<^sub>s. c\<^sub>s' = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                      (\<Gamma>\<^sub>c,(c\<^sub>c, (aa, b), bb),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ab, be), bf),R\<^sub>s,G\<^sub>s))) \<or>
               c\<^sub>c' = While b\<^sub>c c1\<^sub>c \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                 c\<^sub>s' = While b\<^sub>s c1\<^sub>s \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<or>
               c\<^sub>c' = Skip \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Skip \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<and> (aa, b) \<notin> b\<^sub>c \<or>
               c\<^sub>c' = Throw \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Throw \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<gamma>\<^sub>a \<or>
               (\<exists>f. c\<^sub>c' = Fault f \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                    c\<^sub>s' = Fault f \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                   (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
               c\<^sub>c' = Stuck \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Stuck \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', (af, bh), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (a, bd), bc),R\<^sub>s,G\<^sub>s))" 
proof-        
  let ?\<sigma> = "((aa, b), ba)" and ?\<Sigma> = "((ac, bb), bc)" and ?\<sigma>' = "((af, bh), ba)"
  { 
    assume sigb:"fst ?\<sigma> \<in> b\<^sub>c" 
    then have s1c1:"?\<sigma>' =  ?\<sigma> \<and> c\<^sub>c' = Seq c1\<^sub>c (LanguageCon.com.While b\<^sub>c c1\<^sub>c)"
      using dest_while a15 unfolding toSeq_def
      by (metis ComplD fst_conv )
    moreover have Sigb:"fst ?\<Sigma> \<in> b\<^sub>s" using calculation sigb same_set a14 a9  by fastforce
    ultimately have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (While b\<^sub>s c1\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Seq c1\<^sub>s (While b\<^sub>s c1\<^sub>s), toSeq ?\<Sigma>)" 
      unfolding toSeq_def 
      by (simp add: r_into_rtranclp stepce.WhileTruec) 
    moreover have "((?\<sigma>, ?\<sigma>'), ?\<Sigma>,  ?\<Sigma>) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>" 
      using a14 a13 s1c1 a3  unfolding related_transitions_def by blast
    moreover have "(\<Gamma>\<^sub>c,(c1\<^sub>c, ?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1\<^sub>s, ?\<Sigma>),R\<^sub>s,G\<^sub>s)"
      using sigb Sigb a14 a0 a10   unfolding RGSim_pre_def and_rel_def ext_set_def  by blast
    ultimately have ?thesis using s1c1  unfolding related_transitions_def by blast  
  } 
  moreover {    
    assume a00: "fst ?\<sigma> \<in> -b\<^sub>c" 
    then have a00':"fst ?\<Sigma> \<in> -b\<^sub>s" using a14 a9 same_set by blast
    then have ?thesis    
    proof -      
      have f5:"(?\<sigma>,?\<Sigma>)\<in>\<alpha>" 
        using a14  a3 by force      
      then have f4: "\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (While b\<^sub>s c1\<^sub>s, fst ?\<Sigma>) \<rightarrow> (Skip, fst ?\<Sigma>)"
        using  stepce.WhileFalsec a00'  unfolding toSeq_def
        by fast         
      have f6: "?\<sigma>' = ?\<sigma> \<and> (fst ?\<sigma> \<in> - b\<^sub>c \<and> c\<^sub>c' = LanguageCon.com.Skip \<or> 
                fst ?\<sigma> \<in> b\<^sub>c \<and> c\<^sub>c' = LanguageCon.com.Seq c1\<^sub>c (LanguageCon.com.While b\<^sub>c c1\<^sub>c))"
        using a15 dest_while unfolding toSeq_def
        by fastforce
      then have "(( ?\<sigma>, ?\<sigma>'), ?\<Sigma>, ?\<Sigma>) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
        using f5 a13 by (simp add:  a13 related_transitions_def Domain.DomainI)
      then show ?thesis
        using a14 f6 f4 a00 unfolding related_transitions_def toSeq_def
        by auto
    qed      
  }
  ultimately show ?thesis by auto
qed

  lemma while_seq_no_ev3:
"a = Skip \<Longrightarrow>
 \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (a, toSeq ((aa, b), ba)) \<rightarrow> (c\<^sub>c',toSeq ((af, bh), ba)) \<Longrightarrow>
  \<exists>c\<^sub>s' a bd.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((a, bd), bc)) \<and>
          (((af, bh), ba), (a, bd), bc) \<in> \<alpha> \<and>
          (((((aa, b), ba), (af, bh), ba), ((ac, bb), bc), (a, bd), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          ((\<exists>aa b bb ab be bf.
               (\<exists>c\<^sub>c. c\<^sub>c' = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
                      af = aa \<and> bh = b \<and> ba = bb \<and>
                      (\<exists>c\<^sub>s. c\<^sub>s' = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                      (\<Gamma>\<^sub>c,(c\<^sub>c, (aa, b), bb),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ab, be), bf),R\<^sub>s,G\<^sub>s))) \<or>
               c\<^sub>c' = While b\<^sub>c c1\<^sub>c \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                 c\<^sub>s' = While b\<^sub>s c1\<^sub>s \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<or>
               c\<^sub>c' = Skip \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Skip \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<and> (aa, b) \<notin> b\<^sub>c \<or>
               c\<^sub>c' = Throw \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Throw \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<gamma>\<^sub>a \<or>
               (\<exists>f. c\<^sub>c' = Fault f \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                    c\<^sub>s' = Fault f \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                   (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
               c\<^sub>c' = Stuck \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Stuck \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', (af, bh), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (a, bd), bc),R\<^sub>s,G\<^sub>s))"  
    using skip1 by auto
            
lemma while_seq_no_ev4:     
 "a = Throw \<Longrightarrow> 
 \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (a, toSeq ((aa, b), ba)) \<rightarrow> (c\<^sub>c',toSeq ((af, bh), ba)) \<Longrightarrow>
  \<exists>c\<^sub>s' a bd.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((a, bd), bc)) \<and>
          (((af, bh), ba), (a, bd), bc) \<in> \<alpha> \<and>
          (((((aa, b), ba), (af, bh), ba), ((ac, bb), bc), (a, bd), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          ((\<exists>aa b bb ab be bf.
               (\<exists>c\<^sub>c. c\<^sub>c' = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
                      af = aa \<and> bh = b \<and> ba = bb \<and>
                      (\<exists>c\<^sub>s. c\<^sub>s' = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                      (\<Gamma>\<^sub>c,(c\<^sub>c, (aa, b), bb),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ab, be), bf),R\<^sub>s,G\<^sub>s))) \<or>
               c\<^sub>c' = While b\<^sub>c c1\<^sub>c \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                 c\<^sub>s' = While b\<^sub>s c1\<^sub>s \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<or>
               c\<^sub>c' = Skip \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Skip \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<and> (aa, b) \<notin> b\<^sub>c \<or>
               c\<^sub>c' = Throw \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Throw \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<gamma>\<^sub>a \<or>
               (\<exists>f. c\<^sub>c' = Fault f \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                    c\<^sub>s' = Fault f \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                   (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
               c\<^sub>c' = Stuck \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Stuck \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', (af, bh), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (a, bd), bc),R\<^sub>s,G\<^sub>s))"  
    using throw1 by auto


lemma while_seq_no_ev5:
  "a = Fault f \<Longrightarrow> 
 \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (a, toSeq ((aa, b), ba)) \<rightarrow> (c\<^sub>c',toSeq ((af, bh), ba)) \<Longrightarrow>
  \<exists>c\<^sub>s' a bd.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((a, bd), bc)) \<and>
          (((af, bh), ba), (a, bd), bc) \<in> \<alpha> \<and>
          (((((aa, b), ba), (af, bh), ba), ((ac, bb), bc), (a, bd), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          ((\<exists>aa b bb ab be bf.
               (\<exists>c\<^sub>c. c\<^sub>c' = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
                      af = aa \<and> bh = b \<and> ba = bb \<and>
                      (\<exists>c\<^sub>s. c\<^sub>s' = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                      (\<Gamma>\<^sub>c,(c\<^sub>c, (aa, b), bb),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ab, be), bf),R\<^sub>s,G\<^sub>s))) \<or>
               c\<^sub>c' = While b\<^sub>c c1\<^sub>c \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                 c\<^sub>s' = While b\<^sub>s c1\<^sub>s \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<or>
               c\<^sub>c' = Skip \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Skip \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<and> (aa, b) \<notin> b\<^sub>c \<or>
               c\<^sub>c' = Throw \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Throw \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<gamma>\<^sub>a \<or>
               (\<exists>f. c\<^sub>c' = Fault f \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                    c\<^sub>s' = Fault f \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                   (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
               c\<^sub>c' = Stuck \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Stuck \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', (af, bh), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (a, bd), bc),R\<^sub>s,G\<^sub>s))"  
    using Fault_ev by auto

lemma while_seq_no_ev6:
  "a = Stuck \<Longrightarrow>
 \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (a, toSeq ((aa, b), ba)) \<rightarrow> (c\<^sub>c',toSeq ((af, bh), ba)) \<Longrightarrow>
  \<exists>c\<^sub>s' a bd.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((a, bd), bc)) \<and>
          (((af, bh), ba), (a, bd), bc) \<in> \<alpha> \<and>
          (((((aa, b), ba), (af, bh), ba), ((ac, bb), bc), (a, bd), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          ((\<exists>aa b bb ab be bf.
               (\<exists>c\<^sub>c. c\<^sub>c' = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
                      af = aa \<and> bh = b \<and> ba = bb \<and>
                      (\<exists>c\<^sub>s. c\<^sub>s' = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                      (\<Gamma>\<^sub>c,(c\<^sub>c, (aa, b), bb),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ab, be), bf),R\<^sub>s,G\<^sub>s))) \<or>
               c\<^sub>c' = While b\<^sub>c c1\<^sub>c \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                 c\<^sub>s' = While b\<^sub>s c1\<^sub>s \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<or>
               c\<^sub>c' = Skip \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Skip \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<and> (aa, b) \<notin> b\<^sub>c \<or>
               c\<^sub>c' = Throw \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Throw \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<gamma>\<^sub>a \<or>
               (\<exists>f. c\<^sub>c' = Fault f \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                    c\<^sub>s' = Fault f \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                   (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
               c\<^sub>c' = Stuck \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Stuck \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', (af, bh), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (a, bd), bc),R\<^sub>s,G\<^sub>s))"  
    using Stuck_ev by auto

lemma while_seq_no_ev:
  assumes 
  a0:"(\<Gamma>\<^sub>c,c1\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c1\<^sub>s,R\<^sub>s,G\<^sub>s)" and    
  a3:"\<xi> \<subseteq> \<alpha>" and a4':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and  
  a5:"Sta\<^sub>s \<gamma>\<^sub>a (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>" and    
  a8:"\<xi> \<subseteq> \<up>(b\<^sub>c \<rightleftharpoons>  b\<^sub>s)" and
  a9:"\<xi>\<^sub>1 = \<xi> \<inter> \<up>(b\<^sub>c \<odot>  b\<^sub>s)" and    
  a12:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and
  a13:"(\<exists>c\<^sub>c. a = LanguageCon.com.Seq c\<^sub>c (LanguageCon.com.While b\<^sub>c c1\<^sub>c) \<and>
               aa = ad \<and>
               b = bd \<and>
               ba = be \<and>
               (\<exists>c\<^sub>s. ab = LanguageCon.com.Seq c\<^sub>s (LanguageCon.com.While b\<^sub>s c1\<^sub>s) \<and>
                      ac = ae \<and>
                      bb = bf \<and>
                      bc = bg \<and> (\<Gamma>\<^sub>c,(c\<^sub>c, (ad, bd), be),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                      (\<Gamma>\<^sub>s,(c\<^sub>s, (ae, bf), bg),R\<^sub>s,G\<^sub>s))) \<or>
        a = LanguageCon.com.While b\<^sub>c c1\<^sub>c \<and>
        aa = ad \<and>
        b = bd \<and>
        ba = be \<and>
        ab = LanguageCon.com.While b\<^sub>s c1\<^sub>s \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<or>
        a = LanguageCon.com.Skip \<and>
        aa = ad \<and>
        b = bd \<and>
        ba = be \<and>
        ab = LanguageCon.com.Skip \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<and> (ad, bd) \<notin> b\<^sub>c \<or>
        a = LanguageCon.com.Throw \<and>
        aa = ad \<and>
        b = bd \<and>
        ba = be \<and>
        ab = LanguageCon.com.Throw \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<gamma>\<^sub>a \<or>
        (\<exists>f. a = com.Fault f \<and>
             aa = ad \<and>
             b = bd \<and>
             ba = be \<and>
             ab = com.Fault f \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>) \<or>
        a = com.Stuck \<and>
        aa = ad \<and>
        b = bd \<and>
        ba = be \<and> ab = com.Stuck \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>" and
  a14:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (a, toSeq ((aa, b), ba)) \<rightarrow> (c\<^sub>c',toSeq ((af, bh), ba))"
  shows "\<exists>c\<^sub>s' a bd.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((a, bd), bc)) \<and>
          (((af, bh), ba), (a, bd), bc) \<in> \<alpha> \<and>
          (((((aa, b), ba), (af, bh), ba), ((ac, bb), bc), (a, bd), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          ((\<exists>aa b bb ab be bf.
               (\<exists>c\<^sub>c. c\<^sub>c' = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
                      af = aa \<and> bh = b \<and> ba = bb \<and>
                      (\<exists>c\<^sub>s. c\<^sub>s' = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                      (\<Gamma>\<^sub>c,(c\<^sub>c, (aa, b), bb),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ab, be), bf),R\<^sub>s,G\<^sub>s))) \<or>
               c\<^sub>c' = While b\<^sub>c c1\<^sub>c \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                 c\<^sub>s' = While b\<^sub>s c1\<^sub>s \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<or>
               c\<^sub>c' = Skip \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Skip \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<xi> \<and> (aa, b) \<notin> b\<^sub>c \<or>
               c\<^sub>c' = Throw \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Throw \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<gamma>\<^sub>a \<or>
               (\<exists>f. c\<^sub>c' = Fault f \<and> af = aa \<and> bh = b \<and> ba = bb \<and> 
                    c\<^sub>s' = Fault f \<and> a = ab \<and> bd = be \<and> bc = bf \<and> 
                   (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
               c\<^sub>c' = Stuck \<and> af = aa \<and> bh = b \<and> ba = bb \<and> c\<^sub>s' = Stuck \<and> a = ab \<and> bd = be \<and> 
                 bc = bf \<and> (((aa, b), bb), (ab, be), bf) \<in> \<alpha>) \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', (af, bh), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (a, bd), bc),R\<^sub>s,G\<^sub>s))"  
  
proof- 
  show ?thesis using a13 a14 apply auto 
    using while_seq_no_ev1[OF _  a14, of b\<^sub>c c1\<^sub>c ab b\<^sub>s c1\<^sub>s ] apply auto[1]    
    apply (auto  intro: while_seq_no_ev2[OF a0 a3 _  a8 a9 a12 _] simp: a14)
       apply (frule  while_seq_no_ev3[OF  _ a14, of \<Gamma>\<^sub>s ab ac bb bc \<alpha> G\<^sub>c G\<^sub>s b\<^sub>c c1\<^sub>c b\<^sub>s c1\<^sub>s R\<^sub>c \<xi> \<gamma>\<^sub>a R\<^sub>s], simp)
    apply (frule while_seq_no_ev4[OF  _ a14, of \<Gamma>\<^sub>s ab ac bb bc \<alpha> G\<^sub>c G\<^sub>s b\<^sub>c c1\<^sub>c b\<^sub>s c1\<^sub>s R\<^sub>c \<xi> \<gamma>\<^sub>a R\<^sub>s], simp)
 apply (frule while_seq_no_ev5[OF  _ a14, of _ \<Gamma>\<^sub>s ab ac bb bc \<alpha> G\<^sub>c G\<^sub>s b\<^sub>c c1\<^sub>c b\<^sub>s c1\<^sub>s R\<^sub>c \<xi> \<gamma>\<^sub>a R\<^sub>s],simp)
    by(frule  while_seq_no_ev6[OF  _ a14, of \<Gamma>\<^sub>s ab ac bb bc \<alpha> G\<^sub>c G\<^sub>s b\<^sub>c c1\<^sub>c b\<^sub>s c1\<^sub>s R\<^sub>c \<xi> \<gamma>\<^sub>a R\<^sub>s],simp)
qed

lemma while_seq_ev:
   assumes
 a12:"(\<exists>c\<^sub>c. a = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
               aa = ad \<and> b = bd \<and> ba = be \<and>
               (\<exists>c\<^sub>s. ab = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and>
                      ac = ae \<and>
                      bb = bf \<and>
                      bc = bg \<and> (\<Gamma>\<^sub>c,(c\<^sub>c, (ad, bd), be),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                      (\<Gamma>\<^sub>s,(c\<^sub>s, (ae, bf), bg),R\<^sub>s,G\<^sub>s))) \<or>
        a = While b\<^sub>c c1\<^sub>c \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = While b\<^sub>s c1\<^sub>s \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<or>
        a = Skip \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Skip \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<and> (ad, bd) \<notin> b\<^sub>c \<or>
        a = Throw \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Throw \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> 
            (((ad, bd), be), (ae, bf), bg) \<in> \<gamma>\<^sub>a \<or>
        (\<exists>f. a = Fault f \<and> aa = ad \<and> b = bd \<and> ba = be \<and>
             ab = Fault f \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>) \<or>
        a = Stuck \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Stuck \<and> 
             ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>"
 shows "\<forall>v c\<^sub>c' ad bd.
       \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>Some v (a, toSeq ((aa, b), ba)) \<rightarrow> (c\<^sub>c', toSeq ((ad, bd), ba)) \<longrightarrow>
       (\<exists>c\<^sub>s' a be.
           (\<exists>aa ad b.
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (aa, ad, b) \<and>
               (\<exists>ab ac ba.
                   \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (aa, ad, b) \<rightarrow> (ab, ac, ba) \<and>
                   \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, ac, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((a, be), bc)))) \<and>
           (((ad, bd), ba), (a, be), bc) \<in> \<alpha> \<and>
           ((((aa, b), ba), (ad, bd), ba), ((ac, bb), bc), (a, be), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
           ((\<exists>aa b bb ab bf bg.
                (\<exists>c\<^sub>c. c\<^sub>c' = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and> ad = aa \<and> bd = b \<and> ba = bb \<and>
                     (\<exists>c\<^sub>s. c\<^sub>s' = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and> a = ab \<and> be = bf \<and> bc = bg \<and> 
                      (\<Gamma>\<^sub>c,(c\<^sub>c, (aa, b), bb),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ab, bf), bg),R\<^sub>s,G\<^sub>s))) \<or>
                c\<^sub>c' = While b\<^sub>c c1\<^sub>c \<and> ad = aa \<and> bd = b \<and> ba = bb \<and> 
                c\<^sub>s' = While b\<^sub>s c1\<^sub>s \<and> a = ab \<and> be = bf \<and> bc = bg \<and> 
                  (((aa, b), bb), (ab, bf), bg) \<in> \<xi> \<or>
                c\<^sub>c' = Skip \<and> ad = aa \<and> bd = b \<and> ba = bb \<and>
                c\<^sub>s' = Skip \<and> a = ab \<and> be = bf \<and> bc = bg \<and> 
                   (((aa, b), bb), (ab, bf), bg) \<in> \<xi> \<and> (aa, b) \<notin> b\<^sub>c \<or>
                c\<^sub>c' = Throw \<and> ad = aa \<and> bd = b \<and> ba = bb \<and>
                c\<^sub>s' = Throw \<and> a = ab \<and> be = bf \<and> bc = bg \<and> (((aa, b), bb), (ab, bf), bg) \<in> \<gamma>\<^sub>a \<or>
                (\<exists>f. c\<^sub>c' = Fault f \<and> ad = aa \<and> bd = b \<and> ba = bb \<and>
                     c\<^sub>s' = Fault f \<and> a = ab \<and> be = bf \<and> bc = bg \<and> 
                     (((aa, b), bb), (ab, bf), bg) \<in> \<alpha>) \<or>
                c\<^sub>c' = Stuck \<and> ad = aa \<and> bd = b \<and> ba = bb \<and>
                c\<^sub>s' = Stuck \<and> a = ab \<and> be = bf \<and> bc = bg \<and> (((aa, b), bb), (ab, bf), bg) \<in> \<alpha>) \<or>
            (\<Gamma>\<^sub>c,(c\<^sub>c', (ad, bd), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (a, be), bc),R\<^sub>s,G\<^sub>s)))" (is ?goal)     
   using a12 
 proof (auto)
   fix v c\<^sub>c' ada bda  c\<^sub>c c\<^sub>s
   assume a0:"(\<Gamma>\<^sub>c,(c\<^sub>c, (ad, bd), be),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ae, bf), bg),R\<^sub>s,G\<^sub>s)" and
            a1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c), toSeq ((ad, bd), be)) \<rightarrow> (c\<^sub>c', toSeq ((ada, bda), be))"     
   have "c\<^sub>c \<noteq> Throw \<and> c\<^sub>c \<noteq> Skip" 
    using a1 not_seq_skip_throw_ev by fastforce
   then obtain c1'
    where stepc1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) ( c\<^sub>c, toSeq ((ad, bd), be)) \<rightarrow> (c1', toSeq ((ada, bda), be))" and 
          seq:    "(c\<^sub>c',toSeq ((ada, bda), be))= (Seq c1' (While b\<^sub>c c1\<^sub>c),toSeq ((ada, bda), be))" 
     using stepc_elim_cases1(7)[OF a1[simplified ], of "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) ( c\<^sub>c, toSeq ((ad, bd), be)) \<rightarrow> 
                  (c1', toSeq ((ada, bda), be)) \<and> 
                 (c\<^sub>c',toSeq ((ada, bda), be))= (Seq c1' (While b\<^sub>c c1\<^sub>c),toSeq ((ada, bda), be))"]
     by fastforce    
    then show " \<exists>c\<^sub>s' a bea.
              (\<exists>aa ad b.
                  \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq c\<^sub>s (LanguageCon.com.While b\<^sub>s c1\<^sub>s),
                           CRef.toSeq ((ae, bf), bg)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                          (aa, ad, b) \<and>
                  (\<exists>ab ac ba.
                      \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (aa, ad, b) \<rightarrow> (ab, ac, ba) \<and>
                      \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, ac, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', CRef.toSeq ((a, bea), bg)))) \<and>
              (((ada, bda), be), (a, bea), bg) \<in> \<alpha> \<and>
              ((((ad, bd), be), (ada, bda), be), ((ae, bf), bg), (a, bea), bg) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
              ((\<exists>aa b bb ab bf bga.
                   (\<exists>c\<^sub>c. c\<^sub>c' = LanguageCon.com.Seq c\<^sub>c (LanguageCon.com.While b\<^sub>c c1\<^sub>c) \<and>
                          ada = aa \<and>
                          bda = b \<and>
                          be = bb \<and>
                          (\<exists>c\<^sub>s. c\<^sub>s' = LanguageCon.com.Seq c\<^sub>s (LanguageCon.com.While b\<^sub>s c1\<^sub>s) \<and>
                                 a = ab \<and>
                                 bea = bf \<and>
                                 bg = bga \<and> (\<Gamma>\<^sub>c,(c\<^sub>c, (aa, b), bb),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                                 (\<Gamma>\<^sub>s,(c\<^sub>s, (ab, bf), bga),R\<^sub>s,G\<^sub>s))) \<or>
                   c\<^sub>c' = LanguageCon.com.While b\<^sub>c c1\<^sub>c \<and>
                   ada = aa \<and>
                   bda = b \<and>
                   be = bb \<and>
                   c\<^sub>s' = LanguageCon.com.While b\<^sub>s c1\<^sub>s \<and>
                   a = ab \<and> bea = bf \<and> bg = bga \<and> (((aa, b), bb), (ab, bf), bga) \<in> \<xi> \<or>
                   c\<^sub>c' = LanguageCon.com.Skip \<and>
                   ada = aa \<and>
                   bda = b \<and>
                   be = bb \<and>
                   c\<^sub>s' = LanguageCon.com.Skip \<and>
                   a = ab \<and> bea = bf \<and> bg = bga \<and> (((aa, b), bb), (ab, bf), bga) \<in> \<xi> \<and> (aa, b) \<notin> b\<^sub>c \<or>
                   c\<^sub>c' = LanguageCon.com.Throw \<and>
                   ada = aa \<and>
                   bda = b \<and>
                   be = bb \<and>
                   c\<^sub>s' = LanguageCon.com.Throw \<and>
                   a = ab \<and> bea = bf \<and> bg = bga \<and> (((aa, b), bb), (ab, bf), bga) \<in> \<gamma>\<^sub>a \<or>
                   (\<exists>f. c\<^sub>c' = com.Fault f \<and>
                        ada = aa \<and>
                        bda = b \<and>
                        be = bb \<and>
                        c\<^sub>s' = com.Fault f \<and>
                        a = ab \<and> bea = bf \<and> bg = bga \<and> (((aa, b), bb), (ab, bf), bga) \<in> \<alpha>) \<or>
                   c\<^sub>c' = com.Stuck \<and>
                   ada = aa \<and>
                   bda = b \<and>
                   be = bb \<and>
                   c\<^sub>s' = com.Stuck \<and> a = ab \<and> bea = bf \<and> bg = bga \<and> (((aa, b), bb), (ab, bf), bga) \<in> \<alpha>) \<or>
               (\<Gamma>\<^sub>c,(c\<^sub>c', (ada, bda), be),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
               (\<Gamma>\<^sub>s,(c\<^sub>s', (a, bea), bg),R\<^sub>s,G\<^sub>s))"
      using  seq_ev_plus stepc1 seq a0 dest_sim_ev_step[OF a0 stepc1] apply auto
      by fast
  qed(auto elim:  stepc_elim_cases1(9) intro: skip1 throw1 Fault_ev Stuck_ev)

  
lemma dest_sta:"Sta\<^sub>s r R \<Longrightarrow> ((x1,y1),(x2,y2))\<in>R \<Longrightarrow> (x1,x2) \<in> r \<Longrightarrow> (y1,y2)\<in> r"
  unfolding Sta\<^sub>s_def by auto

lemma not_stable_false: assumes a0:"Sta\<^sub>s (\<xi> \<inter> \<up>((- b\<^sub>c) \<odot>  (- b\<^sub>s))) (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>" and
         a2:"\<xi> \<subseteq> \<up>(b\<^sub>c \<rightleftharpoons>  b\<^sub>s)" and
     a3:"((((ad, bd), be), (af, bh), bi), ((ae, bf), bg), (ag, bj), bk) \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>"
    and a4:"(((ad, bd), be), (ae, bf), bg) \<in> \<xi>" and a5:"(ad, bd) \<notin> b\<^sub>c" and a6:"(af, bh) \<in> b\<^sub>c"
  shows "False"
proof-
  have "(ae,bf) \<notin> b\<^sub>s" using a5 a4 a2 unfolding eq_rel_def ext_set_def by auto
  then have d:"(((ad, bd), be), (ae, bf), bg)\<in> (\<xi> \<inter> \<up>((- b\<^sub>c) \<odot>  (- b\<^sub>s)))" 
    using a4 a5 unfolding  and_rel_def ext_set_def by fastforce
  then have "(((af, bh), bi),  (ag, bj), bk) \<in> (\<xi> \<inter> \<up>((- b\<^sub>c) \<odot>  (- b\<^sub>s)))"
    using dest_sta[OF a0 a3 d] by auto
  thus ?thesis using a6 unfolding and_rel_def ext_set_def by auto
qed


lemma while_seq_env:"
       \<xi> \<subseteq> \<alpha> \<Longrightarrow> \<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c \<Longrightarrow>
       Sta\<^sub>s \<xi> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow>
       Sta\<^sub>s \<gamma>\<^sub>a (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow>
       Sta\<^sub>s (\<xi> \<inter> \<up>((- b\<^sub>c) \<odot>  (- b\<^sub>s))) (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow> 
       \<xi>1 = (\<xi> \<inter> \<up>((- b\<^sub>c) \<odot>  (- b\<^sub>s))) \<Longrightarrow>     
       \<xi> \<subseteq> \<up>(b\<^sub>c \<rightleftharpoons>  b\<^sub>s) \<Longrightarrow>             
       (\<exists>c\<^sub>c. a = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
               aa = ad \<and> b = bd \<and> ba = be \<and>
               (\<exists>c\<^sub>s. ab = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and>
                      ac = ae \<and>
                      bb = bf \<and>
                      bc = bg \<and> (\<Gamma>\<^sub>c,(c\<^sub>c, (ad, bd), be),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                      (\<Gamma>\<^sub>s,(c\<^sub>s, (ae, bf), bg),R\<^sub>s,G\<^sub>s))) \<or>
        a = While b\<^sub>c c1\<^sub>c \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = While b\<^sub>s c1\<^sub>s \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<or>
        a = Skip \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Skip \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<and> (ad, bd) \<notin> b\<^sub>c \<or>
        a = Throw \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Throw \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> 
            (((ad, bd), be), (ae, bf), bg) \<in> \<gamma>\<^sub>a \<or>
        (\<exists>f. a = Fault f \<and> aa = ad \<and> b = bd \<and> ba = be \<and>
             ab = Fault f \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>) \<or>
        a = Stuck \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Stuck \<and> 
             ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha> \<Longrightarrow> 
   ((((aa, b), ba), (af, bh), bi), ((ac, bb), bc), (ag, bj), bk) \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow>
    (\<exists>aa b ba ac bb bc.
               (\<exists>c\<^sub>c. a = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and> af = aa \<and> bh = b \<and>
                      bi = ba \<and>
                      (\<exists>c\<^sub>s. ab = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and> ag = ac \<and> bj = bb \<and> bk = bc \<and> 
                      (\<Gamma>\<^sub>c,(c\<^sub>c, (aa, b), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, (ac, bb), bc),R\<^sub>s,G\<^sub>s))) \<or>
               a = While b\<^sub>c c1\<^sub>c \<and> af = aa \<and>
               bh = b \<and> bi = ba \<and> ab = While b\<^sub>s c1\<^sub>s \<and>
               ag = ac \<and> bj = bb \<and> bk = bc \<and> (((aa, b), ba), (ac, bb), bc) \<in> \<xi> \<or>
               a = Skip \<and> af = aa \<and> bh = b \<and> bi = ba \<and>
               ab = Skip \<and>
               ag = ac \<and> bj = bb \<and> bk = bc \<and> (((aa, b), ba), (ac, bb), bc) \<in> \<xi> \<and> (aa, b) \<notin> b\<^sub>c \<or>
               a = Throw \<and> af = aa \<and> bh = b \<and> bi = ba \<and> ab = Throw \<and>
               ag = ac \<and> bj = bb \<and> bk = bc \<and> (((aa, b), ba), (ac, bb), bc) \<in> \<gamma>\<^sub>a \<or>
               (\<exists>f. a = Fault f \<and> af = aa \<and> bh = b \<and> bi = ba \<and>
                    ab = Fault f \<and> ag = ac \<and> bj = bb \<and> bk = bc \<and> (((aa, b), ba), (ac, bb), bc) \<in> \<alpha>) \<or>
               a = Stuck \<and> af = aa \<and> bh = b \<and> bi = ba \<and>
               ab = Stuck \<and> ag = ac \<and> bj = bb \<and> bk = bc \<and> (((aa, b), ba), (ac, bb), bc) \<in> \<alpha>) \<or>
       (\<Gamma>\<^sub>c, (a, (af, bh), bi),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>1\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(ab, (ag, bj), bk),R\<^sub>s,G\<^sub>s)"  
  apply auto 
        apply (metis dest_sim_env_step) 
     apply (auto dest:sim_env intro: not_stable_false)            
  by (auto simp add:  related_transitions_def)
  

lemma while_seq_skip: 
assumes        
       a3:"\<xi> \<subseteq> \<alpha>" and                            
       a8:"\<xi> \<subseteq>  \<up>(b\<^sub>c \<rightleftharpoons>  b\<^sub>s)" and       
       a12:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and
       a13:"(\<exists>c\<^sub>c. a = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
               aa = ad \<and> b = bd \<and> ba = be \<and>
               (\<exists>c\<^sub>s. ab = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and>
                      ac = ae \<and>
                      bb = bf \<and>
                      bc = bg \<and> (\<Gamma>\<^sub>c,(c\<^sub>c, (ad, bd), be),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                      (\<Gamma>\<^sub>s,(c\<^sub>s, (ae, bf), bg),R\<^sub>s,G\<^sub>s))) \<or>
        a = While b\<^sub>c c1\<^sub>c \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = While b\<^sub>s c1\<^sub>s \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<or>
        a = Skip \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Skip \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<and> (ad, bd) \<notin> b\<^sub>c \<or>
        a = Throw \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Throw \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> 
            (((ad, bd), be), (ae, bf), bg) \<in> \<gamma>\<^sub>a \<or>
        (\<exists>f. a = Fault f \<and> aa = ad \<and> b = bd \<and> ba = be \<and>
             ab = Fault f \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>) \<or>
        a = Stuck \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Stuck \<and> 
             ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>" and
      a14:"a = Skip "
       shows
        " \<exists>a bd.
              ((((aa, b), ba), (aa, b), ba), ((ac, bb), bc), (a, bd), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
              (((aa, b), ba), (a, bd), bc) \<in> \<xi> \<and>
              (((aa, b), ba), (a, bd), bc) \<in> \<up>((- b\<^sub>c) \<odot>  (- b\<^sub>s)) \<and>
              \<xi> \<inter> \<up>((- b\<^sub>c) \<odot>  (- b\<^sub>s)) \<subseteq> \<alpha> \<and>
              (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeq ((a, bd), bc)))"        
proof -       
  have "a = LanguageCon.com.Skip \<and>
        ab = LanguageCon.com.Skip \<and>
      (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<and> (ad, bd) \<notin> b\<^sub>c "
    using a14 a13 by auto
 
  have "((((ad, bd), be), ((ad, bd), be)),(((ae, bf), bg), ((ae, bf), bg))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>" 
  proof -
    have "(((ad, bd), be), (ae, bf), bg) \<in> \<alpha>"
      using a3 a14 a13  by auto    
    then show ?thesis
      by (simp add:a12 alpha_id_G  related_transitions_def Domain.DomainI)
  qed  
  moreover have "(((ad, bd), be), (ae, bf), bg) \<in> \<up>((- b\<^sub>c) \<odot>  (- b\<^sub>s))"
     using a8 calculation a13 a14   unfolding and_rel_def ext_set_def eq_rel_def 
     by fastforce   
  ultimately show  " \<exists>a bd.
              ((((aa, b), ba), (aa, b), ba), ((ac, bb), bc), (a, bd), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
              (((aa, b), ba), (a, bd), bc) \<in> \<xi> \<and>
              (((aa, b), ba), (a, bd), bc) \<in> \<up>((- b\<^sub>c) \<odot>  (- b\<^sub>s)) \<and>
              \<xi> \<inter> \<up>((- b\<^sub>c) \<odot>  (- b\<^sub>s)) \<subseteq> \<alpha> \<and>
              (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeq ((a, bd), bc)))"   
     using a3 a13 a14  by auto
 qed        

lemma while_seq_throw: 
assumes        
       a3:"\<xi> \<subseteq> \<alpha>" and a3':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and                            
       a12:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and
       a13:"(\<exists>c\<^sub>c. a = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
               aa = ad \<and> b = bd \<and> ba = be \<and>
               (\<exists>c\<^sub>s. ab = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and>
                      ac = ae \<and>
                      bb = bf \<and>
                      bc = bg \<and> (\<Gamma>\<^sub>c,(c\<^sub>c, (ad, bd), be),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                      (\<Gamma>\<^sub>s,(c\<^sub>s, (ae, bf), bg),R\<^sub>s,G\<^sub>s))) \<or>
        a = While b\<^sub>c c1\<^sub>c \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = While b\<^sub>s c1\<^sub>s \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<or>
        a = Skip \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Skip \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<and> (ad, bd) \<notin> b\<^sub>c \<or>
        a = Throw \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Throw \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> 
            (((ad, bd), be), (ae, bf), bg) \<in> \<gamma>\<^sub>a \<or>
        (\<exists>f. a = Fault f \<and> aa = ad \<and> b = bd \<and> ba = be \<and>
             ab = Fault f \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>) \<or>
        a = Stuck \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Stuck \<and> 
             ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>" and 
     a14:"a = LanguageCon.com.Throw "
       shows
        "\<exists>a bd.
                ((((aa, b), ba), (aa, b), ba), ((ac, bb), bc), (a, bd), bc) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                (((aa, b), ba), (a, bd), bc) \<in> \<gamma>\<^sub>a \<and>
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, CRef.toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                        (LanguageCon.com.Throw, CRef.toSeq ((a, bd), bc))"
        
proof -  
  
  have "((((ad, bd), be), ((ad, bd), be)),(((ae, bf), bg), ((ae, bf), bg))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>" 
  proof -
    have "(((ad, bd), be), (ae, bf), bg) \<in> \<alpha>"
      using a3' a14 a13  by auto    
    then show ?thesis
      by (simp add:a12 alpha_id_G  related_transitions_def DomainI)
   qed    
   then show "\<exists>a bd.
                ((((aa, b), ba), (aa, b), ba), ((ac, bb), bc), (a, bd), bc) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                (((aa, b), ba), (a, bd), bc) \<in> \<gamma>\<^sub>a \<and>
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, CRef.toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                        (LanguageCon.com.Throw, CRef.toSeq ((a, bd), bc))" 
     using a3 a3' a14 a13   by fastforce 
 qed        


lemma while_seq_fault: 
assumes                                           
       a12:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and
       a13:"(\<exists>c\<^sub>c. a = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
               aa = ad \<and> b = bd \<and> ba = be \<and>
               (\<exists>c\<^sub>s. ab = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and>
                      ac = ae \<and>
                      bb = bf \<and>
                      bc = bg \<and> (\<Gamma>\<^sub>c,(c\<^sub>c, (ad, bd), be),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                      (\<Gamma>\<^sub>s,(c\<^sub>s, (ae, bf), bg),R\<^sub>s,G\<^sub>s))) \<or>
        a = While b\<^sub>c c1\<^sub>c \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = While b\<^sub>s c1\<^sub>s \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<or>
        a = Skip \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Skip \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<and> (ad, bd) \<notin> b\<^sub>c \<or>
        a = Throw \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Throw \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> 
            (((ad, bd), be), (ae, bf), bg) \<in> \<gamma>\<^sub>a \<or>
        (\<exists>f. a = Fault f \<and> aa = ad \<and> b = bd \<and> ba = be \<and>
             ab = Fault f \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>) \<or>
        a = Stuck \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Stuck \<and> 
             ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>" and 
     a14:"a = Fault f "
       shows
        "\<exists>a bd.
              ((((aa, b), ba), (aa, b), ba), ((ac, bb), bc), (a, bd), bc) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, CRef.toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (com.Fault f, CRef.toSeq ((a, bd), bc)) \<and>
              (((aa, b), ba), (a, bd), bc) \<in> \<alpha>"
        
proof -  
  
  have "((((ad, bd), be), ((ad, bd), be)),(((ae, bf), bg), ((ae, bf), bg))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>" 
  proof -
    have "(((ad, bd), be), (ae, bf), bg) \<in> \<alpha>"
      using  a14 a13  by auto    
    then show ?thesis
      by (simp add:a12 alpha_id_G  related_transitions_def DomainI)
   qed    
   then show "\<exists>a bd.
              ((((aa, b), ba), (aa, b), ba), ((ac, bb), bc), (a, bd), bc) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, CRef.toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq ((a, bd), bc)) \<and>
              (((aa, b), ba), (a, bd), bc) \<in> \<alpha>" 
     using a14 a13  by fast 
 qed  

lemma while_seq_stuck: 
assumes                                           
       a12:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and
       a13:"(\<exists>c\<^sub>c. a = Seq c\<^sub>c (While b\<^sub>c c1\<^sub>c) \<and>
               aa = ad \<and> b = bd \<and> ba = be \<and>
               (\<exists>c\<^sub>s. ab = Seq c\<^sub>s (While b\<^sub>s c1\<^sub>s) \<and>
                      ac = ae \<and>
                      bb = bf \<and>
                      bc = bg \<and> (\<Gamma>\<^sub>c,(c\<^sub>c, (ad, bd), be),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                      (\<Gamma>\<^sub>s,(c\<^sub>s, (ae, bf), bg),R\<^sub>s,G\<^sub>s))) \<or>
        a = While b\<^sub>c c1\<^sub>c \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = While b\<^sub>s c1\<^sub>s \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<or>
        a = Skip \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Skip \<and>
        ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<xi> \<and> (ad, bd) \<notin> b\<^sub>c \<or>
        a = Throw \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Throw \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> 
            (((ad, bd), be), (ae, bf), bg) \<in> \<gamma>\<^sub>a \<or>
        (\<exists>f. a = Fault f \<and> aa = ad \<and> b = bd \<and> ba = be \<and>
             ab = Fault f \<and> ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>) \<or>
        a = Stuck \<and> aa = ad \<and> b = bd \<and> ba = be \<and> ab = Stuck \<and> 
             ac = ae \<and> bb = bf \<and> bc = bg \<and> (((ad, bd), be), (ae, bf), bg) \<in> \<alpha>" and 
     a14:"a = Stuck"
       shows
        "\<exists>a bd.
              ((((aa, b), ba), (aa, b), ba), ((ac, bb), bc), (a, bd), bc) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck,toSeq ((a, bd), bc)) \<and>
              (((aa, b), ba), (a, bd), bc) \<in> \<alpha>"
        
proof -  
  
  have "((((ad, bd), be), ((ad, bd), be)),(((ae, bf), bg), ((ae, bf), bg))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>" 
  proof -
    have "(((ad, bd), be), (ae, bf), bg) \<in> \<alpha>"
      using  a14 a13  by auto    
    then show ?thesis
      by (simp add:a12 alpha_id_G  related_transitions_def DomainI)
   qed    
   then show "\<exists>a bd.
              ((((aa, b), ba), (aa, b), ba), ((ac, bb), bc), (a, bd), bc) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ab, toSeq ((ac, bb), bc)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck,toSeq ((a, bd), bc)) \<and>
              (((aa, b), ba), (a, bd), bc) \<in> \<alpha>"
     using a14 a13  by fast 
 qed   

lemma while_sim:
  "(\<Gamma>\<^sub>c,c1\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c1\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow>
   (\<sigma>,\<Sigma>)\<in>\<xi> \<Longrightarrow>   
   \<xi> \<subseteq> \<alpha> \<Longrightarrow> \<gamma>\<^sub>a\<subseteq>\<alpha> \<Longrightarrow>
  Sta\<^sub>s \<xi> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow>
  Sta\<^sub>s \<gamma>\<^sub>a (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow> 
  Sta\<^sub>s \<gamma>\<^sub>n (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow> 
  \<xi> \<subseteq>  \<up>(b\<^sub>c \<rightleftharpoons>  b\<^sub>s) \<Longrightarrow>
   \<xi>\<^sub>1 = \<xi> \<inter>  \<up>(b\<^sub>c \<odot>  b\<^sub>s) \<Longrightarrow>
   \<gamma>\<^sub>n = \<xi> \<inter>  \<up>((- b\<^sub>c) \<odot>  (- b\<^sub>s)) \<Longrightarrow>   
   \<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c \<Longrightarrow> 
   (\<Gamma>\<^sub>c,(While b\<^sub>c c1\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(While b\<^sub>s c1\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s)"
apply (coinduct taking:"coPre \<xi> b\<^sub>c b\<^sub>s \<Gamma>\<^sub>c c1\<^sub>c R\<^sub>c G\<^sub>c \<alpha> \<gamma>\<^sub>n \<gamma>\<^sub>a \<Gamma>\<^sub>s c1\<^sub>s R\<^sub>s G\<^sub>s"  rule:RGSim.coinduct) 
   apply (simp add:coPre_def, clarsimp simp add:coPre_def)
  apply (rule conjI, rule while_seq_alpha[of \<xi> \<alpha> \<gamma>\<^sub>a], assumption+)
  apply (rule conjI, rule, rule, rule, rule, rule while_seq_no_ev, simp+)    
  apply (rule conjI, rule while_seq_ev, assumption+)   
  apply (rule conjI, rule, rule,rule, rule, rule, rule, rule, rule while_seq_env, assumption+, simp+)      
  apply (rule conjI, rule, rule while_seq_skip, assumption+)   
  apply (rule conjI, rule, rule while_seq_throw, assumption+) 
  apply (rule conjI,rule, rule, rule while_seq_fault, assumption+) 
  by (rule, rule while_seq_stuck, assumption+)
        
    
lemma While_sound:    
    "\<xi> \<subseteq> \<alpha> \<Longrightarrow> Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow> \<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c \<Longrightarrow> 
     \<xi> \<subseteq> \<up>(b\<^sub>c \<rightleftharpoons> b\<^sub>s) \<Longrightarrow> \<xi>\<^sub>1= \<xi> \<inter> \<up>(b\<^sub>c \<odot> b\<^sub>s) \<Longrightarrow> \<gamma>\<^sub>n= \<xi> \<inter> \<up>((-b\<^sub>c) \<odot> (-b\<^sub>s) ) \<Longrightarrow>
  (\<Gamma>\<^sub>c,c\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<xi>\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow> Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow> Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow> \<gamma>\<^sub>a\<subseteq>\<alpha> \<Longrightarrow>
  (\<Gamma>\<^sub>c,While b\<^sub>c c\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,While b\<^sub>s c\<^sub>s,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def apply (simp, rule, rule,rule,rule, rule,rule,rule)
  apply (rule while_sim[of \<Gamma>\<^sub>c c\<^sub>c R\<^sub>c G\<^sub>c \<alpha> \<xi>\<^sub>1 \<xi> \<gamma>\<^sub>a \<Gamma>\<^sub>s c\<^sub>s R\<^sub>s G\<^sub>s])
  unfolding RGSim_pre_def by fastforce+


lemma DynCom_sim:    
  assumes
     a1:"\<xi> \<subseteq> \<alpha>" and 
   a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and 
   a6:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and
   a7:"\<forall>\<sigma> \<Sigma>. (\<sigma>,\<Sigma>)\<in> \<xi> \<longrightarrow> (\<Gamma>\<^sub>c,(f\<^sub>c (fst \<sigma>),\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(f\<^sub>s (fst \<Sigma>), \<Sigma>),R\<^sub>s,G\<^sub>s)" and
   a8:"(\<sigma>,\<Sigma>)\<in> \<xi>" 
 shows "(\<Gamma>\<^sub>c,(DynCom f\<^sub>c,  \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(DynCom f\<^sub>s,  \<Sigma>),R\<^sub>s,G\<^sub>s)" 
   using  a1   a3  a6 a7 a8        
    apply(coinduction arbitrary: \<sigma> \<Sigma>)
      apply(clarsimp)
   apply (rule conjId)+
(* not Normal transition*)
   apply (meson sim_env)                    
(* Event Component transition *)
      apply (rule, rule, rule, rule,rule)     
      apply (auto elim: ev_stepc_normal_elim_cases)     
      (* silent component transition *)        
    apply (auto     elim:stepc_elim_cases1(12))
   apply (erule stepc_elim_cases1(12), auto)   
   using a7 DomainI unfolding toSeq_def apply auto
   by (smt Domain.DomainI r_into_rtranclp related_transition_intro rtrancl.rtrancl_refl 
          rtrancl_idemp stepce.DynComc subsetD) 

                   
lemma DynCom_sound:    
    "\<xi> \<subseteq> \<alpha>  \<Longrightarrow>
   Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow>  
    \<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c \<Longrightarrow> 
   \<forall>\<sigma> \<Sigma>. (\<sigma>,\<Sigma>)\<in>\<xi> \<longrightarrow> (\<Gamma>\<^sub>c,(f\<^sub>c (fst \<sigma>),\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(f\<^sub>s (fst \<Sigma>), \<Sigma>),R\<^sub>s,G\<^sub>s) \<Longrightarrow>  
  (\<Gamma>\<^sub>c,DynCom f\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,DynCom f\<^sub>s,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def apply (rule, rule, rule)
  apply (rule DynCom_sim)
  unfolding RGSim_pre_def by blast+

inductive_cases stepc_guard_cases:
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Guard f g c, s) \<rightarrow> (c', s')"

lemma Guard_sim:
  assumes 
  a1:"\<xi> \<subseteq> \<alpha> " and 
  a2:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and 
  a3:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and  
  a5:"\<xi> \<subseteq> \<up>(b\<^sub>c \<rightleftharpoons> b\<^sub>s)" and a6:"\<xi>\<^sub>1 = \<xi> \<inter> \<up>(b\<^sub>c \<odot> b\<^sub>s)" and
  a8:"(\<sigma>,\<Sigma>)\<in>\<xi>" and
  a9:"(\<Gamma>\<^sub>c,c\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c\<^sub>s,R\<^sub>s,G\<^sub>s)"
shows  
  "(\<Gamma>\<^sub>c,(Guard f b\<^sub>c c\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Guard f b\<^sub>s c\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s)"
  using a1 a2 a3  a6  a8 a9 
proof(coinduction arbitrary: \<sigma>  \<Sigma>,clarsimp)         
  fix \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls 
  let ?s1 = "(\<forall>c\<^sub>c' \<sigma>g' \<sigma>l'.
               \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Guard f b\<^sub>c c\<^sub>c, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow>
                        (c\<^sub>c', CRef.toSeq ((\<sigma>g', \<sigma>l'), \<sigma>ls)) \<longrightarrow>
               (\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
                   \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Guard f b\<^sub>s c\<^sub>s, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                           (c\<^sub>s', toSeq ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<and>
                   (((\<sigma>g', \<sigma>l'), \<sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> \<alpha> \<and>
                   ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g', \<sigma>l'), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                   (c\<^sub>c' = Guard f b\<^sub>c c\<^sub>c \<and>
                    c\<^sub>s' = Guard f b\<^sub>s c\<^sub>s \<and> (((\<sigma>g', \<sigma>l'), \<sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> \<xi> \<or>
                    (\<Gamma>\<^sub>c,(c\<^sub>c', (\<sigma>g', \<sigma>l'), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (\<Sigma>g', \<Sigma>l'), \<Sigma>ls),R\<^sub>s,G\<^sub>s))))"
    assume 
       a0:"(((\<sigma>g,\<sigma>l), \<sigma>ls), ((\<Sigma>g,\<Sigma>l), \<Sigma>ls)) \<in> \<xi>" and              
       a3:"Sta\<^sub>s \<xi> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>" and                           
       a8:"\<xi> \<subseteq> \<alpha>" and              
       a12:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c"    
    have alpha:"(((\<sigma>g,\<sigma>l), \<sigma>ls), ((\<Sigma>g,\<Sigma>l), \<Sigma>ls)) \<in> \<alpha>" 
      using a0 a8  by auto
    moreover have "\<forall>\<sigma>g' \<sigma>l' \<sigma>ls' \<Sigma>g' \<Sigma>l' \<Sigma>ls'.
           ((((\<sigma>g,\<sigma>l), \<sigma>ls),((\<sigma>g',\<sigma>l'), \<sigma>ls')), 
               (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls'))) \<in> ((R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<longrightarrow>
           ((((\<sigma>g',\<sigma>l'), \<sigma>ls'), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls')) \<in> \<xi>) \<or>
           (\<Gamma>\<^sub>c,(LanguageCon.com.Guard f b\<^sub>c c\<^sub>c, ((\<sigma>g',\<sigma>l'), \<sigma>ls')),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
           (\<Gamma>\<^sub>s,(LanguageCon.com.Guard f b\<^sub>s c\<^sub>s, ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls')),R\<^sub>s,G\<^sub>s)" 
      using env[OF a0 a3] by blast
    moreover have "
           \<forall>v c\<^sub>c' \<sigma>g' \<sigma>l'.
               \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Guard f b\<^sub>c c\<^sub>c, toSeq ((\<sigma>g,\<sigma>l), \<sigma>ls)) \<rightarrow>
                              (c\<^sub>c', toSeq ((\<sigma>g',\<sigma>l'), \<sigma>ls)) \<longrightarrow>
               (\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
                   (\<exists>a ab b.
                       \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Guard f b\<^sub>s c\<^sub>s, toSeq ((\<Sigma>g,\<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                       (\<exists>aa ad ba.
                           \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, ab, b) \<rightarrow> (aa, ad, ba) \<and>
                           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ad, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)))) \<and>
                   (((\<sigma>g',\<sigma>l'), \<sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)) \<in> \<alpha> \<and>
                   ((((\<sigma>g,\<sigma>l), \<sigma>ls),((\<sigma>g',\<sigma>l'), \<sigma>ls)), 
                       (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls))) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                   (c\<^sub>c' = Guard f b\<^sub>c c\<^sub>c \<and>
                    c\<^sub>s' = Guard f b\<^sub>s c\<^sub>s \<and> (((\<sigma>g',\<sigma>l'), \<sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)) \<in> \<xi> \<or>
                    (\<Gamma>\<^sub>c,(c\<^sub>c', ((\<sigma>g',\<sigma>l'), \<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)),R\<^sub>s,G\<^sub>s)))"
      by (fastforce elim: stepc_guard_cases)            
    moreover have ?s1      
    proof -
    {
      fix c\<^sub>c' \<sigma>g' \<sigma>l'
      assume  a00:" \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Guard f b\<^sub>c c\<^sub>c, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((\<sigma>g', \<sigma>l'), \<sigma>ls))"      
      have guar1:"((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), 
                    ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (\<Sigma>g, \<Sigma>l), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
        using a12  a0 a8  unfolding related_transitions_def Id_def by blast             
      have h:"((c\<^sub>c'=c\<^sub>c \<and> (\<sigma>g', \<sigma>l')\<in>b\<^sub>c) \<or> (c\<^sub>c' = Fault f \<and> (\<sigma>g', \<sigma>l')\<notin> b\<^sub>c)) \<and> \<sigma>g'= \<sigma>g \<and> \<sigma>l'= \<sigma>l"
        using stepc_elim_cases2(2)[OF a00] unfolding toSeq_def by auto
      { assume a000:" (\<sigma>g, \<sigma>l)\<in>b\<^sub>c"
        then have step:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Guard f b\<^sub>c c\<^sub>c, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<and> 
                         \<sigma>g'= \<sigma>g \<and> \<sigma>l'= \<sigma>l"
          using a00 h by auto
        then have sig1:"c\<^sub>c'=c\<^sub>c \<and> ((((\<sigma>g,\<sigma>l), \<sigma>ls), ((\<Sigma>g,\<Sigma>l), \<Sigma>ls))) \<in> \<xi>\<^sub>1"
          using a0 a5 a6 h a000   unfolding eq_rel_def  and_rel_def ext_set_def by auto
        then have sn_inb:"c\<^sub>c'=c\<^sub>c \<and> (\<Sigma>g,\<Sigma>l)\<in>b\<^sub>s" 
          using a6 a5 a0 unfolding and_rel_def eq_rel_def ext_set_def by auto
        then have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Guard f b\<^sub>s c\<^sub>s, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s, (\<Sigma>g,\<Sigma>l))" 
          using sn_inb stepce.Guardc GuardFaultc
          by fast                 
        have "(\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Guard f b\<^sub>s c\<^sub>s, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                   (c\<^sub>s', CRef.toSeq ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<and>
           (((\<sigma>g', \<sigma>l'), \<sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> \<alpha> \<and>
           ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g', \<sigma>l'), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
           (c\<^sub>c' = LanguageCon.com.Guard f b\<^sub>c c\<^sub>c \<and>
            c\<^sub>s' = LanguageCon.com.Guard f b\<^sub>s c\<^sub>s \<and> (((\<sigma>g', \<sigma>l'), \<sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> \<xi> \<or>
            (\<Gamma>\<^sub>c,(c\<^sub>c', (\<sigma>g', \<sigma>l'), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (\<Sigma>g', \<Sigma>l'), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))"
            using  steps guar1  a9  sig1 step a3 
            unfolding related_transitions_def RGSim_pre_def toSeq_def
            by fastforce
      }
      moreover { assume a000:"(\<sigma>g, \<sigma>l)\<notin>b\<^sub>c"
        then have sig1:"c\<^sub>c' = Fault f \<and> ((((\<sigma>g,\<sigma>l), \<sigma>ls), ((\<Sigma>g,\<Sigma>l), \<Sigma>ls))) \<notin> \<xi>\<^sub>1"
          using a0 a5 a6 h  unfolding eq_rel_def  and_rel_def ext_set_def by auto
        then have sn_inb:"c\<^sub>c' = Fault f \<and>(\<Sigma>g,\<Sigma>l)\<notin>b\<^sub>s" 
          using a6 a5 a0 unfolding and_rel_def eq_rel_def ext_set_def by auto
        then have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Guard f b\<^sub>s c\<^sub>s, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, (\<Sigma>g,\<Sigma>l))" 
          using sn_inb  GuardFaultc h a000
          by fast                 
        have "(\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Guard f b\<^sub>s c\<^sub>s, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                   (c\<^sub>s', CRef.toSeq ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<and>
           (((\<sigma>g', \<sigma>l'), \<sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> \<alpha> \<and>
           ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g', \<sigma>l'), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
           (c\<^sub>c' = LanguageCon.com.Guard f b\<^sub>c c\<^sub>c \<and>
            c\<^sub>s' = LanguageCon.com.Guard f b\<^sub>s c\<^sub>s \<and> (((\<sigma>g', \<sigma>l'), \<sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> \<xi> \<or>
            (\<Gamma>\<^sub>c,(c\<^sub>c', (\<sigma>g', \<sigma>l'), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (\<Sigma>g', \<Sigma>l'), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))"
          using  h steps guar1  a9  sig1 Fault_sim[OF alpha assms(3)] alpha  
          unfolding related_transitions_def RGSim_pre_def toSeq_def by fastforce                                    
      } ultimately have "(\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Guard f b\<^sub>s c\<^sub>s, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                   (c\<^sub>s', CRef.toSeq ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<and>
           (((\<sigma>g', \<sigma>l'), \<sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> \<alpha> \<and>
           ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g', \<sigma>l'), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
           (c\<^sub>c' = LanguageCon.com.Guard f b\<^sub>c c\<^sub>c \<and>
            c\<^sub>s' = LanguageCon.com.Guard f b\<^sub>s c\<^sub>s \<and> (((\<sigma>g', \<sigma>l'), \<sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> \<xi> \<or>
            (\<Gamma>\<^sub>c,(c\<^sub>c', (\<sigma>g', \<sigma>l'), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (\<Sigma>g', \<Sigma>l'), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))" by auto      
     } thus ?thesis by auto
   qed     
   ultimately show "(((\<sigma>g,\<sigma>l), \<sigma>ls), ((\<Sigma>g,\<Sigma>l), \<Sigma>ls)) \<in> \<alpha> \<and> ?s1 \<and>
           (\<forall>v c\<^sub>c' \<sigma>g' \<sigma>l'.
               \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Guard f b\<^sub>c c\<^sub>c, toSeq ((\<sigma>g,\<sigma>l), \<sigma>ls)) \<rightarrow>
                              (c\<^sub>c', toSeq ((\<sigma>g',\<sigma>l'), \<sigma>ls)) \<longrightarrow>
               (\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
                   (\<exists>a ab b.
                       \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Guard f b\<^sub>s c\<^sub>s, toSeq ((\<Sigma>g,\<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                       (\<exists>aa ad ba.
                           \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, ab, b) \<rightarrow> (aa, ad, ba) \<and>
                           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ad, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)))) \<and>
                   (((\<sigma>g',\<sigma>l'), \<sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)) \<in> \<alpha> \<and>
                   ((((\<sigma>g,\<sigma>l), \<sigma>ls),((\<sigma>g',\<sigma>l'), \<sigma>ls)), 
                       (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls))) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                   (c\<^sub>c' = Guard f b\<^sub>c c\<^sub>c \<and>
                    c\<^sub>s' = Guard f b\<^sub>s c\<^sub>s \<and> (((\<sigma>g',\<sigma>l'), \<sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)) \<in> \<xi> \<or>
                    (\<Gamma>\<^sub>c,(c\<^sub>c', ((\<sigma>g',\<sigma>l'), \<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)),R\<^sub>s,G\<^sub>s)))) \<and>
           (\<forall>\<sigma>g' \<sigma>l' \<sigma>ls' \<Sigma>g' \<Sigma>l' \<Sigma>ls'.
           ((((\<sigma>g,\<sigma>l), \<sigma>ls),((\<sigma>g',\<sigma>l'), \<sigma>ls')), 
               (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls'))) \<in> ((R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<longrightarrow>
           ((((\<sigma>g',\<sigma>l'), \<sigma>ls'), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls')) \<in> \<xi>) \<or>
           (\<Gamma>\<^sub>c,(LanguageCon.com.Guard f b\<^sub>c c\<^sub>c, ((\<sigma>g',\<sigma>l'), \<sigma>ls')),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
           (\<Gamma>\<^sub>s,(LanguageCon.com.Guard f b\<^sub>s c\<^sub>s, ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls')),R\<^sub>s,G\<^sub>s)) "
      by auto
  qed    
   
                       
lemma Guard_sound:    
 " \<xi> \<subseteq> \<alpha> \<Longrightarrow> Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow> \<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c \<Longrightarrow> 
   \<xi> \<subseteq> \<up>(b\<^sub>c \<rightleftharpoons> b\<^sub>s) \<Longrightarrow> \<xi>\<^sub>1= \<xi> \<inter> \<up>(b\<^sub>c \<odot> b\<^sub>s) \<Longrightarrow>  
  (\<Gamma>\<^sub>c,c\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow>  
  (\<Gamma>\<^sub>c,Guard f b\<^sub>c c\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,Guard f b\<^sub>s c\<^sub>s,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def apply (rule, rule, rule)
  apply (rule Guard_sim)
  unfolding RGSim_pre_def by blast+
    
definition f_equiv  ("_ \<rightleftharpoons>\<^sub>f / _" [81,81] 100) 
where
"
f_equiv \<Gamma>\<^sub>c \<Gamma>\<^sub>s \<equiv>  (\<Gamma>\<^sub>c =None \<and> \<Gamma>\<^sub>s = None) \<or> ((\<exists>pc. \<Gamma>\<^sub>c = Some pc) \<and> (\<exists>ps. \<Gamma>\<^sub>s = Some ps))
"

inductive_cases stepc_call_cases:
"\<Gamma>\<turnstile>\<^sub>c\<^sub>e(Call ps, s) \<rightarrow> (c', s')"

lemma Call_sim:
  assumes 
  a1:"\<xi> \<subseteq> \<alpha> " and 
  a2:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and 
  a3:"\<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c" and   
  a5:"(\<Gamma>\<^sub>c pc) \<rightleftharpoons>\<^sub>f (\<Gamma>\<^sub>s ps)" and 
  a6:"(\<forall>c\<^sub>c c\<^sub>s. \<Gamma>\<^sub>c pc = Some c\<^sub>c \<and> \<Gamma>\<^sub>s ps = Some c\<^sub>s \<longrightarrow> (\<Gamma>\<^sub>c,c\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c\<^sub>s,R\<^sub>s,G\<^sub>s))" and
  a8:"(\<sigma>,\<Sigma>)\<in>\<xi>" 
shows  
  "(\<Gamma>\<^sub>c,(Call pc, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Call ps, \<Sigma>),R\<^sub>s,G\<^sub>s)" 
using a1 a2    a5 a6  a8 
proof(coinduction arbitrary: \<sigma> \<Sigma>,clarsimp)  
  fix  \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls 
    assume  
       a0:"(((\<sigma>g,\<sigma>l), \<sigma>ls), ((\<Sigma>g,\<Sigma>l), \<Sigma>ls)) \<in> \<xi>" and              
       a2:"Sta\<^sub>s \<xi> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>" and                           
       a8:"\<xi> \<subseteq> \<alpha>"  
    have alpha:"(((\<sigma>g,\<sigma>l), \<sigma>ls), ((\<Sigma>g,\<Sigma>l), \<Sigma>ls)) \<in> \<alpha>" 
      using a0 a8  by auto    
    moreover have "\<forall>a b ba aa bb bc.
            ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), ba), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, bb), bc) \<in> ((R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<longrightarrow>
            (((a, b), ba), (aa, bb), bc) \<in> \<xi> \<or> (\<Gamma>\<^sub>c,(LanguageCon.com.Call pc, (a, b), ba),R\<^sub>c,G\<^sub>c)
            \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(LanguageCon.com.Call ps, (aa, bb), bc),R\<^sub>s,G\<^sub>s)" 
      using env[OF a0 a2] by blast    
    moreover have "\<forall>v c\<^sub>c' a b.
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Call pc,toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((a, b), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                (\<exists>a ab b.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Call ps, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                    (\<exists>ac ad bb.
                        \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, ab, b) \<rightarrow> (ac, ad, bb) \<and>
                        \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ac, ad, bb) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', CRef.toSeq ((aa, ba), \<Sigma>ls)))) \<and>
                (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                (c\<^sub>c' = Call pc \<and>
                 c\<^sub>s' = Call ps \<and> (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))"
      by (fastforce elim: stepc_call_cases) 
    moreover have "\<forall>c\<^sub>c' \<sigma>g' \<sigma>l'.
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Call pc, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((\<sigma>g', \<sigma>l'), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Call ps, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',  toSeq ((aa, ba), \<Sigma>ls)) \<and>
                (((\<sigma>g', \<sigma>l'), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g', \<sigma>l'), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                (c\<^sub>c' = Call pc \<and>
                 c\<^sub>s' = Call ps \<and> (((\<sigma>g', \<sigma>l'), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', (\<sigma>g', \<sigma>l'), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))"
    proof -
      {fix c\<^sub>c' \<sigma>g' \<sigma>l'
        assume  a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Call pc,  toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c',   toSeq ((\<sigma>g', \<sigma>l'), \<sigma>ls))"
        have guar1:"((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), 
                    ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (\<Sigma>g, \<Sigma>l), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
        using a3  a0 a8  unfolding related_transitions_def Id_def by blast              
        have h:"((\<exists>c\<^sub>c. \<Gamma>\<^sub>c pc = Some c\<^sub>c) \<and> c\<^sub>c' = the (\<Gamma>\<^sub>c pc) \<or> 
              \<not>(\<exists>c\<^sub>c. \<Gamma>\<^sub>c pc = Some c\<^sub>c) \<and> c\<^sub>c' = Stuck ) \<and>  \<sigma>g'= \<sigma>g \<and> \<sigma>l'= \<sigma>l" 
          using stepc_elim_cases1(11)[OF a00, 
             of "((\<exists>c\<^sub>c. \<Gamma>\<^sub>c pc = Some c\<^sub>c) \<and> c\<^sub>c' = the (\<Gamma>\<^sub>c pc) \<or> 
                \<not>(\<exists>c\<^sub>c. \<Gamma>\<^sub>c pc = Some c\<^sub>c) \<and> c\<^sub>c' = Stuck ) \<and>  \<sigma>g'= \<sigma>g \<and> \<sigma>l'= \<sigma>l"] unfolding toSeq_def 
          by fastforce 
        { assume a000:"\<exists>c\<^sub>c. \<Gamma>\<^sub>c pc = Some c\<^sub>c"
          then obtain c\<^sub>s where someps:"\<Gamma>\<^sub>s ps = Some c\<^sub>s"
             using a5 unfolding f_equiv_def by auto                       
          then have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Call ps, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (the (\<Gamma>\<^sub>s ps), toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls))" 
            using a5 someps
            by (metis  option.distinct(1) option.exhaust_sel 
                    r_into_rtranclp rtranclp.rtrancl_refl stepce.Callc)               
          then have "(\<Gamma>\<^sub>c,c\<^sub>c',R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c\<^sub>s,R\<^sub>s,G\<^sub>s)"
            using someps a6 h a000 by fastforce
          then have "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Call pc, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((\<sigma>g', \<sigma>l'), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Call ps, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',  toSeq ((aa, ba), \<Sigma>ls)) \<and>
                (((\<sigma>g', \<sigma>l'), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g', \<sigma>l'), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                (c\<^sub>c' = Call pc \<and>
                 c\<^sub>s' = Call ps \<and> (((\<sigma>g', \<sigma>l'), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', (\<sigma>g', \<sigma>l'), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))" 
          using  steps guar1 a6 h  unfolding related_transitions_def RGSim_pre_def  
          using someps a0 by fastforce
      }
      moreover{
        assume a000:"\<not>(\<exists>c\<^sub>c. \<Gamma>\<^sub>c pc = Some c\<^sub>c)"
        then have "\<Gamma>\<^sub>c pc = None" by auto
        then have "\<Gamma>\<^sub>s ps = None" using a5 unfolding f_equiv_def by auto
        then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Call ps, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck,  toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls))"
          unfolding toSeq_def                        
          by (simp add: r_into_rtranclp stepce.CallUndefinedc)
        then have "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Call pc, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((\<sigma>g', \<sigma>l'), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Call ps, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',  toSeq ((aa, ba), \<Sigma>ls)) \<and>
                (((\<sigma>g', \<sigma>l'), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g', \<sigma>l'), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                (c\<^sub>c' = Call pc \<and>
                 c\<^sub>s' = Call ps \<and> (((\<sigma>g', \<sigma>l'), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', (\<sigma>g', \<sigma>l'), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))" 
          using alpha Stuck_sim[OF alpha assms(3)] h a000  guar1 by blast
          
      } 
      ultimately have "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Call pc, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((\<sigma>g', \<sigma>l'), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Call ps, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',  toSeq ((aa, ba), \<Sigma>ls)) \<and>
                (((\<sigma>g', \<sigma>l'), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g', \<sigma>l'), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                (c\<^sub>c' = Call pc \<and>
                 c\<^sub>s' = Call ps \<and> (((\<sigma>g', \<sigma>l'), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', (\<sigma>g', \<sigma>l'), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))" 
        by auto
    } thus ?thesis by auto
  qed    
  ultimately show 
      "(((\<sigma>g, \<sigma>l), \<sigma>ls), (\<Sigma>g, \<Sigma>l), \<Sigma>ls) \<in> \<alpha> \<and>
        (\<forall>c\<^sub>c' a b.
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Call pc, CRef.toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', CRef.toSeq ((a, b), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Call ps, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                        (c\<^sub>s', CRef.toSeq ((aa, ba), \<Sigma>ls)) \<and>
                (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                (c\<^sub>c' = LanguageCon.com.Call pc \<and>
                 c\<^sub>s' = LanguageCon.com.Call ps \<and> (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))) \<and>
        (\<forall>v c\<^sub>c' a b.
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>Some v (LanguageCon.com.Call pc, CRef.toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow>
                           (c\<^sub>c', CRef.toSeq ((a, b), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                (\<exists>a ab b.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Call ps, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                    (\<exists>ac ad bb.
                        \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, ab, b) \<rightarrow> (ac, ad, bb) \<and>
                        \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ac, ad, bb) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', CRef.toSeq ((aa, ba), \<Sigma>ls)))) \<and>
                (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                (c\<^sub>c' = LanguageCon.com.Call pc \<and>
                 c\<^sub>s' = LanguageCon.com.Call ps \<and> (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))) \<and>
        (\<forall>a b ba aa bb bc.
            ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), ba), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, bb), bc) \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<longrightarrow>
            (((a, b), ba), (aa, bb), bc) \<in> \<xi> \<or> (\<Gamma>\<^sub>c,(LanguageCon.com.Call pc, (a, b), ba),R\<^sub>c,G\<^sub>c)
            \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(LanguageCon.com.Call ps, (aa, bb), bc),R\<^sub>s,G\<^sub>s))" 
      by auto   
qed   

 lemma Call_sound:    
 " \<xi> \<subseteq> \<alpha>  \<Longrightarrow> Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow> \<forall>a b ba. ((a, b), ba) \<in> Domain \<alpha> \<longrightarrow> (((a, b), ba), (a, b), ba) \<in> G\<^sub>c \<Longrightarrow> 
   (\<Gamma>\<^sub>c pc) \<rightleftharpoons>\<^sub>f (\<Gamma>\<^sub>s ps) \<Longrightarrow> 
  (\<forall>c\<^sub>c c\<^sub>s. \<Gamma>\<^sub>c pc = Some c\<^sub>c \<and> \<Gamma>\<^sub>s ps = Some c\<^sub>s \<longrightarrow> (\<Gamma>\<^sub>c,c\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c\<^sub>s,R\<^sub>s,G\<^sub>s)) \<Longrightarrow>   
  (\<Gamma>\<^sub>c,Call pc,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,Call ps,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def apply (rule, rule, rule)
  apply (rule Call_sim)
  unfolding RGSim_pre_def by auto 
   
type_synonym ('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula =  
   "(('gc\<times>'lc,'p,'f,'e) com \<times>     
     (('gc,'lc)par_state)  rel1 \<times> 
     (('gc,'lc)par_state) rel1 \<times> 
     ('gs\<times>'ls,'p,'f,'e) com \<times>     
     (('gs,'ls)par_state)  rel1 \<times> 
     (('gs,'ls)par_state) rel1 \<times> 
     (('gc,'lc)par_state,('gs,'ls)par_state) rel \<times>
     (('gc,'lc)par_state,('gs,'ls)par_state) rel \<times>
     (('gc,'lc)par_state,('gs,'ls)par_state) rel 
    )" 
   
 definition Com\<^sub>c:: "('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula \<Rightarrow> ('gc\<times>'lc,'p,'f,'e) com" where
  "Com\<^sub>c f \<equiv> fst f"

  definition Rel\<^sub>c :: "('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula \<Rightarrow> (('gc,'lc)par_state)  rel1" where
  "Rel\<^sub>c f \<equiv> fst (snd f)" 

 definition Gua\<^sub>c :: "('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula \<Rightarrow> (('gc,'lc)par_state)  rel1" where
  "Gua\<^sub>c f \<equiv> fst (snd (snd f))" 
  
 definition Com\<^sub>s:: "('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula \<Rightarrow> ('gs\<times>'ls,'p,'f,'e) com" where
  "Com\<^sub>s f \<equiv> fst (snd (snd (snd f)))"
  
 definition Rel\<^sub>s :: "('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula \<Rightarrow> (('gs,'ls)par_state)  rel1" where
  "Rel\<^sub>s f \<equiv>  fst (snd (snd (snd (snd f))))" 

 definition Gua\<^sub>s :: "('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula \<Rightarrow> (('gs,'ls)par_state)  rel1" where
  "Gua\<^sub>s f \<equiv>  fst (snd (snd (snd (snd (snd f)))))"
 
definition Pre :: "('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula \<Rightarrow> 
                     (('gc,'lc)par_state,('gs,'ls)par_state) rel " where
   "Pre f \<equiv>  fst (snd (snd (snd (snd (snd (snd f))))))" 

 definition PostQ :: " ('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula \<Rightarrow> 
                     (('gc,'lc)par_state,('gs,'ls)par_state) rel " where
   "PostQ f \<equiv>  fst (snd (snd (snd (snd (snd (snd (snd f)))))))" 
 
 definition PostA :: "('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula \<Rightarrow> 
                     (('gc,'lc)par_state,('gs,'ls)par_state) rel " where
   "PostA f \<equiv>  snd (snd (snd (snd (snd (snd (snd (snd f)))))))" 

    
definition PCom\<^sub>c :: "('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula list \<Rightarrow> ('gc,'lc,'p,'f,'e) par_com"
where
"PCom\<^sub>c Ps \<equiv> map Com\<^sub>c Ps"

definition PCom\<^sub>s :: "('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula list \<Rightarrow> ('gs,'ls,'p,'f,'e) par_com"
where
"PCom\<^sub>s Ps \<equiv> map Com\<^sub>s Ps"

definition par_sim_list :: "(('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula  \<Rightarrow>'b) \<Rightarrow> 
                           ('gc,'lc,'gs,'ls,'p,'f,'e) parallel_sim_formula  list \<Rightarrow> 'b list"
where
"par_sim_list f Ps \<equiv> map f Ps"


lemma ParallelCom_Com:"i<length xs \<Longrightarrow> (par_sim_list Com\<^sub>s xs)!i = Com\<^sub>s (xs!i)"
unfolding par_sim_list_def Com\<^sub>s_def by fastforce    


  
lemma G_comp_aux': 
"g\<subseteq>G \<and> (s2, s2') \<in>g\<^sup>* \<Longrightarrow> (s2, s2') \<in> G\<^sup>*"
  by (metis rtrancl_eq_or_trancl trancl_mono)

lemma G_comp_aux: 
assumes a1:"(\<Union>j<length g. g ! j) \<subseteq> G" and
        a2:"(s2, s2') \<in> (g ! i)\<^sup>* " and
        a3:"i < length g"
      shows "(s2, s2') \<in> G\<^sup>*"
using a1 a2 a3 G_comp_aux'
  by (metis UN_subset_iff lessThan_iff)
    
lemma G_comp_aux1: 
assumes a1:"g \<subseteq> G" and
        a2:"(s2, s2') \<in> g\<^sup>* "
      shows "(s2, s2') \<in> G\<^sup>*"
  using a1 a2  G_comp_aux' by metis

lemma tran_G:
  assumes "(s,s')\<in>G\<^sup>*" and "(s',s'')\<in>G\<^sup>*" 
  shows "(s,s'')\<in>G\<^sup>*"
  using  assms by auto
    
lemma G_comp:
  assumes a1:"(\<Union>j<length G1. (G1 !j)) \<subseteq> G\<^sub>1" and
          a2:" (\<Union>j<length G2. (G2 ! j)) \<subseteq> G\<^sub>2"  and
          a3:"((s1, s1'), s2, s2') \<in> (G1 ! i, (G2 ! i)\<^sup>*)\<^sub>\<alpha>" and
          a4:"i<length G1 \<and> i< length G2"
  shows "((s1, s1'), s2, s2') \<in> (G\<^sub>1, G\<^sub>2\<^sup>*)\<^sub>\<alpha>"  
proof-
  have "(s1, s1') \<in> G\<^sub>1" using a1 a3 a4 unfolding related_transitions_def by auto
  moreover have "(s2, s2') \<in> G\<^sub>2\<^sup>*" 
    using a2 a3 a4 G_comp_aux 
    unfolding related_transitions_def by auto
  ultimately show ?thesis using a3 unfolding related_transitions_def by auto
qed
  
lemma G_comp1:
  assumes a1:"G1 \<subseteq> G\<^sub>1" and
          a2:" G2 \<subseteq> G\<^sub>2"  and
          a3:"((s1, s1'), s2, s2') \<in> (G1, G2\<^sup>*)\<^sub>\<alpha>" 
  shows "((s1, s1'), s2, s2') \<in> (G\<^sub>1, G\<^sub>2\<^sup>*)\<^sub>\<alpha>"  
proof-
  have "(s1, s1') \<in> G\<^sub>1" using a1 a3  unfolding related_transitions_def by auto
  moreover have "(s2, s2') \<in> G\<^sub>2\<^sup>*" 
    using a2 a3 G_comp_aux1 
    unfolding related_transitions_def by auto
  ultimately show ?thesis using a3 unfolding related_transitions_def by auto
qed  

    
lemma sim_comp_not_mod:
  assumes a0:"(\<Gamma>\<^sub>c, (c\<^sub>c,\<sigma>),R\<^sub>c, G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,s\<^sub>s),R\<^sub>s, G\<^sub>s)" and
          a1:"(((\<sigma>,s\<^sub>c'),s\<^sub>s,s\<^sub>s') \<in> (R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" 
  shows "(\<Gamma>\<^sub>c, (c\<^sub>c,s\<^sub>c'),R\<^sub>c, G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,s\<^sub>s'),R\<^sub>s, G\<^sub>s)"
  using a0 a1 env_sim by blast
    
definition R_wf::"nat \<Rightarrow> (('\<sigma>g\<times>'\<sigma>l list), ('\<Sigma>g\<times>'\<Sigma>l list)) rel \<Rightarrow> bool"
  where "R_wf i \<alpha> \<equiv> \<forall>\<sigma>g \<sigma>l \<Sigma>g \<Sigma>l. ((\<sigma>g, \<sigma>l),(\<Sigma>g, \<Sigma>l)) \<in> \<alpha> \<longrightarrow> 
                       length \<sigma>l = length \<Sigma>l \<and> i = length \<sigma>l"

(* definition R_wf'::"nat \<Rightarrow> (('\<sigma>g\<times>'\<sigma>l list), ('\<Sigma>g\<times>'\<Sigma>l list)) rel \<Rightarrow> bool"
  where "R_wf' i \<alpha> \<equiv> \<forall>\<sigma>g \<sigma>l \<Sigma>g \<Sigma>l. ((\<sigma>g, \<sigma>l),(\<Sigma>g, \<Sigma>l)) \<in> \<alpha> \<longrightarrow> 
                       length \<sigma>l = length \<Sigma>l \<and> i \<le> length \<sigma>l" *)

lemma eq_step:"(\<forall>j\<noteq>i. \<sigma>'ls ! j = \<sigma>ls ! j) \<Longrightarrow> 
         \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c, CRef.toSeq (toSeqState i (\<sigma>g, \<sigma>ls))) \<rightarrow>
          (c', CRef.toSeq ((\<sigma>'g, (\<sigma>'ls!i)), snd (toSeqState i (\<sigma>g, \<sigma>ls)))) = 
         \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (c, toSeqPar  i (\<sigma>g,\<sigma>ls)) \<rightarrow> (c',  toSeqPar i (\<sigma>'g,\<sigma>'ls))"
unfolding toSeq_def toSeqState_def by auto

definition Rel_wf::"nat \<Rightarrow> (('\<sigma>g\<times>'\<sigma>l list), ('\<Sigma>g\<times>'\<Sigma>l list)) rel \<Rightarrow> bool"
  where "Rel_wf i R \<equiv> \<forall>(x,y)\<in>R. i<length (snd x) \<and> i<length (snd y)"

lemma  toSeqPar_toSeq_SeqState:"CRef.toSeq (toSeqState i (\<sigma>g, \<sigma>ls)) = toSeqPar  i (\<sigma>g,\<sigma>ls)"
  unfolding toSeq_def toSeqState_def by auto

lemma Seq_rel_par':"((toSeqState i (g, ls), toSeqState i (g', ls'))) \<in> Seq_rel i R \<Longrightarrow> 
         Rel_wf i R  \<Longrightarrow>  i< length ls \<Longrightarrow> i< length ls' \<Longrightarrow>
       ((g, ls), (g',ls')) \<in> R"     
  unfolding Seq_rel_def Rel_wf_def apply auto using eq_toSeqState
  by (metis case_prodD snd_conv)
 

lemma Seq_rel_par:"((toSeqState i (g, ls), toSeqState i (g', ls'))) \<in> Seq_rel i R \<Longrightarrow> 
         R_wf (length ls') R \<Longrightarrow>  i< length ls \<Longrightarrow>  length ls = length ls' \<Longrightarrow>
       ((g, ls), (g',ls')) \<in> R"     
  unfolding Seq_rel_def R_wf_def apply auto using eq_toSeqState
  by metis

lemma par_rel_seq_rel:
     "((g, ls), (g',ls')) \<in> R \<Longrightarrow> 
       R_wf (length ls') R \<Longrightarrow>  i< length ls \<Longrightarrow>  length ls = length ls' \<Longrightarrow> 
          ((toSeqState i (g, ls), toSeqState i (g', ls'))) \<in> Seq_rel i R
       "     
  unfolding Seq_rel_def R_wf_def   
  by (metis (no_types, lifting) case_prod_conv image_iff) 

lemma par_rel_seq_rel':
     "((g, ls), (g',ls')) \<in> R \<Longrightarrow> 
       Rel_wf i R \<Longrightarrow>  i< length ls \<Longrightarrow>  i < length ls' \<Longrightarrow> 
          ((toSeqState i (g, ls), toSeqState i (g', ls'))) \<in> Seq_rel i R
       "     
  unfolding Seq_rel_def R_wf_def   
  by (metis (no_types, lifting) case_prod_conv image_iff) 

 

lemma Seq_rel_tran_par:
    "(toSeqState i (g, ls), toSeqState i (g', ls')) \<in> (Seq_rel i R)\<^sup>+ \<Longrightarrow>
        R_wf (length ls) R \<Longrightarrow> i < length ls \<Longrightarrow> length ls = length ls' \<Longrightarrow>         
      ((g, ls),toParState i ( toSeqState i (g', ls'))) \<in> R\<^sup>+"
proof (induct rule:Transitive_Closure.trancl_induct[case_names Refl Step])
  case (Refl y)
  have len:"length (snd y) = length ls - 1" 
    using Refl(1,2,3) unfolding Seq_rel_def apply auto
    by (simp add: R_wf_def len_toSeqState)     
  then have  "toSeqState i (toParState i y) = y"
    using Par2Seq0f 
    by (metis One_nat_def Refl.prems(2) Suc_pred 
           length_greater_0_conv less_Suc_eq_le list.size(3) not_less0)
  moreover have "length (snd (toParState i y)) = length ls" using len
    by (metis Refl.prems(2) Seq2Par len_toParState len_toSeqState snd_conv)
  ultimately show ?case using Seq_rel_par
    by (metis Refl.hyps Refl.prems(1) Refl.prems(2) prod.exhaust_sel trancl.r_into_trancl) 
next
  case (Step y z)
  then have len:"length (snd y) = length ls - 1 \<and> length (snd z) = length ls - 1" 
    using Step(1) unfolding Seq_rel_def apply auto    
    by (auto simp add: R_wf_def len_toSeqState) 
  then have "toSeqState i (toParState i y) = y"
    by (metis Nat.le_diff_conv2 One_nat_def Par2Seq0f Step.prems(2) 
        Suc_leI add.commute neq0_conv not_less_zero plus_1_eq_Suc)
  moreover have "toSeqState i (toParState i z) = z" using len 
    by (metis Nat.le_diff_conv2 One_nat_def Par2Seq0f Step.prems(2) 
        Suc_leI add.commute neq0_conv not_less_zero plus_1_eq_Suc)
  ultimately have "(toParState i y, toParState i z) \<in> R" using Step(2) Seq_rel_par len len_toParState
    by (metis One_nat_def Step.prems(1) Step.prems(2) Suc_leI gr0I gr_implies_not0 
          le_add_diff_inverse2 len_toParState prod.exhaust_sel)
  then show ?case using Step by auto
qed   

lemma Seq_rel_tran_par':
    "(toSeqState i (g, ls), toSeqState i (g', ls')) \<in> (Seq_rel i R)\<^sup>+ \<Longrightarrow>
        Rel_wf i R \<Longrightarrow> i < length ls \<Longrightarrow>  i < length ls' \<Longrightarrow>         
      ((g, ls),toParState i ( toSeqState i (g', ls'))) \<in> R\<^sup>+"
proof (induct rule:Transitive_Closure.trancl_induct[case_names Refl Step])
  case (Refl y)
  have len:"i\<le>length (snd y)" 
    using Refl(1,2,3) unfolding Seq_rel_def Rel_wf_def apply (auto simp add: split_def)
    by (metis One_nat_def Suc_pred len_toSeqState length_greater_0_conv 
          less_Suc_eq_le less_trans list.size(3) not_le_imp_less snd_conv)         
  then have  "toSeqState i (toParState i y) = y"
    using Par2Seq0f by fast
  moreover have "i < length (snd (toParState i y))" using len
    using par_seq_rel_i_length toParState_in_rel by blast
  ultimately show ?case using Seq_rel_par'
    by (metis Refl.hyps Refl.prems(1) Refl.prems(2) prod.exhaust_sel trancl.r_into_trancl) 
next
  case (Step y z)
  then have len:"i\<le>length (snd y) \<and> i\<le>length (snd z)" 
    using Step(1) unfolding Seq_rel_def apply auto    
    by (auto simp add: Rel_wf_def len_toSeqState) 
  then have "toSeqState i (toParState i y) = y" using Par2Seq0f by fast
  moreover have "toSeqState i (toParState i z) = z" using len  Par2Seq0f by fast
  ultimately have "(toParState i y, toParState i z) \<in> R" 
    using Step(2) Seq_rel_par' len len_toParState
    by (metis Step.prems(1) i_less_toSeq le_neq_implies_less less_add_one prod.exhaust_sel)
  then show ?case using Step by auto
qed   

lemma par_Seq_rel_tran:
    " ((g, ls), (g', ls')) \<in> R\<^sup>+ \<Longrightarrow>
        R_wf (length ls) R \<Longrightarrow> i < length ls \<Longrightarrow> length ls = length ls'\<Longrightarrow>
       (toSeqState i (g, ls), toSeqState i (g', ls')) \<in> (Seq_rel i R)\<^sup>+         
      " 
proof (induct rule:Transitive_Closure.trancl_induct[case_names Refl Step])
  case (Refl y)          
  then have  "toParState i (toSeqState i y) = y"    
    by (metis R_wf_def Seq2Par prod.exhaust_sel)   
  have f1: "\<forall>p. p = (fst p::'a, snd p::'b list)"
    by simp
  then have "length ls = length (snd y)"
    by (metis (no_types) R_wf_def Refl.hyps Refl.prems(1))
  then show ?case
    using f1 by (metis Refl.hyps Refl.prems(1) Refl.prems(2) par_rel_seq_rel trancl.r_into_trancl)    
next
  case (Step y z)  
  obtain y1 y2 z1 z2 where r:"((y1,y2), (z1,z2))\<in>R"  and "y=(y1,y2)" and "z=(z1,z2)"
    using Step.hyps(2)
    by (metis prod.exhaust_sel)
  then have "(toSeqState i  y,  toSeqState i z) \<in> Seq_rel i R" unfolding R_wf_def
    using Step.prems(1) Step.prems(2) par_rel_seq_rel[OF r]
    by (metis R_wf_def)    
  then show ?case using Step by auto
qed   

lemma Seq_rel_tran_clor_par:"((toSeqState i (g, ls), toSeqState i (g', ls'))) \<in> (Seq_rel i R)\<^sup>* \<Longrightarrow> 
         R_wf (length ls') R \<Longrightarrow>  i< length ls \<Longrightarrow>  length ls = length ls' \<Longrightarrow>
       ((g, ls), (g',ls')) \<in> R\<^sup>*"   
  apply (erule converse_rtranclE)
   apply (metis eq_toSeqState rtrancl.rtrancl_refl)
  using Seq_rel_tran_par
  by (metis (no_types, lifting) Seq2Par rtrancl_into_trancl2 trancl_into_rtrancl)  


lemma par_Seq_rel_tran':
    " ((g, ls), (g', ls')) \<in> R\<^sup>+ \<Longrightarrow>
        Rel_wf i R \<Longrightarrow> i < length ls \<Longrightarrow> i < length ls'\<Longrightarrow>
       (toSeqState i (g, ls), toSeqState i (g', ls')) \<in> (Seq_rel i R)\<^sup>+         
      " 
proof (induct rule:Transitive_Closure.trancl_induct[case_names Refl Step])
  case (Refl y)          
  then have  "toParState i (toSeqState i y) = y"
    by (metis (no_types, lifting) Seq2Par Sim_Rules.Rel_wf_def case_prodD prod.exhaust_sel)
  have f1: "\<forall>p. p = (fst p::'a, snd p::'b list)"
    by simp
  then have "i < length (snd y)" using Rel_wf_def Refl.hyps Refl.prems(1)
    by blast
  then show ?case
    by (metis Refl.hyps Refl.prems(1) Refl.prems(2) par_rel_seq_rel' 
                prod.exhaust_sel trancl.r_into_trancl)       
next
  case (Step y z)  
  obtain y1 y2 z1 z2 where r:"((y1,y2), (z1,z2))\<in>R"  and "y=(y1,y2)" and "z=(z1,z2)"
    using Step.hyps(2)
    by (metis prod.exhaust_sel)
  then have "(toSeqState i  y,  toSeqState i z) \<in> Seq_rel i R" unfolding Rel_wf_def
    using Step.prems(1) Step.prems(2) par_rel_seq_rel'[OF r]
    using Sim_Rules.Rel_wf_def by fastforce
  then show ?case using Step by auto
qed  

lemma Seq_rel_tran_clor_par':"((toSeqState i (g, ls), toSeqState i (g', ls'))) \<in> (Seq_rel i R)\<^sup>* \<Longrightarrow> 
         Rel_wf i R \<Longrightarrow>  i< length ls \<Longrightarrow>  i < length ls' \<Longrightarrow>
       ((g, ls), (g',ls')) \<in> R\<^sup>*"   
  apply (erule converse_rtranclE)
   apply (metis eq_toSeqState rtrancl.rtrancl_refl)
  using Seq_rel_tran_par'
  by (metis (no_types, lifting) Seq2Par rtrancl_into_trancl2 trancl_into_rtrancl) 

lemma par_Seq_rel_tran_clor:"((g, ls), (g',ls')) \<in> R\<^sup>* \<Longrightarrow>  
         R_wf (length ls') R \<Longrightarrow>  i< length ls \<Longrightarrow>  length ls = length ls' \<Longrightarrow>
     ((toSeqState i (g, ls), toSeqState i (g', ls'))) \<in> (Seq_rel i R)\<^sup>*
       "   
  apply (erule converse_rtranclE)
   apply (metis rtrancl.rtrancl_refl)  
  by (simp add: par_Seq_rel_tran rtrancl_into_trancl2 trancl_into_rtrancl)  

lemma par_Seq_rel_tran_clor':"((g, ls), (g',ls')) \<in> R\<^sup>* \<Longrightarrow>  
         Rel_wf i R \<Longrightarrow>  i< length ls \<Longrightarrow>  i < length ls' \<Longrightarrow>
     ((toSeqState i (g, ls), toSeqState i (g', ls'))) \<in> (Seq_rel i R)\<^sup>*
       "   
  apply (erule converse_rtranclE)
   apply (metis rtrancl.rtrancl_refl)  
  by (simp add: par_Seq_rel_tran' rtrancl_into_trancl2 trancl_into_rtrancl) 

lemma rel_tran_seq:"((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>'g, \<sigma>'ls)), 
         (toSeqState i (\<Sigma>g, \<Sigma>ls), toSeqState i (\<Sigma>'g, \<Sigma>'ls))) \<in> 
         (Seq_rel i G\<^sub>c, (Seq_rel i G\<^sub>s)\<^sup>*)\<^sub>Seq_rel i \<alpha> \<Longrightarrow> i < length \<sigma>ls \<Longrightarrow>
         R_wf (length \<sigma>ls) \<alpha> \<Longrightarrow> R_wf (length \<sigma>ls) G\<^sub>c \<Longrightarrow> R_wf (length \<sigma>ls) G\<^sub>s \<Longrightarrow>
         length \<sigma>'ls = length \<sigma>ls \<Longrightarrow> length \<sigma>ls = length \<Sigma>ls \<Longrightarrow>  
         length \<Sigma>ls =  length \<Sigma>'ls \<Longrightarrow>  
         (((\<sigma>g,\<sigma>ls), (\<sigma>'g,\<sigma>'ls)), (\<Sigma>g, \<Sigma>ls), (\<Sigma>'g, \<Sigma>'ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
  unfolding related_transitions_def 
  apply auto using Seq_rel_par apply fastforce using Seq_rel_tran_clor_par apply metis
  using Seq_rel_par apply fastforce using Seq_rel_par by fastforce 

lemma rel_tran_seq':"((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>'g, \<sigma>'ls)), 
         (toSeqState i (\<Sigma>g, \<Sigma>ls), toSeqState i (\<Sigma>'g, \<Sigma>'ls))) \<in> 
         (Seq_rel i G\<^sub>c, (Seq_rel i G\<^sub>s)\<^sup>*)\<^sub>Seq_rel i \<alpha> \<Longrightarrow> i < length \<sigma>ls \<Longrightarrow>
         Rel_wf i \<alpha> \<Longrightarrow> Rel_wf i G\<^sub>c \<Longrightarrow> Rel_wf i G\<^sub>s \<Longrightarrow>
         i < length \<sigma>'ls \<Longrightarrow> i < length \<sigma>ls \<Longrightarrow> i < length \<Sigma>ls  \<Longrightarrow>  
         i <  length \<Sigma>'ls \<Longrightarrow>  
         (((\<sigma>g,\<sigma>ls), (\<sigma>'g,\<sigma>'ls)), (\<Sigma>g, \<Sigma>ls), (\<Sigma>'g, \<Sigma>'ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
  unfolding related_transitions_def 
  apply auto using Seq_rel_par' apply fastforce using Seq_rel_tran_clor_par' apply metis
  using Seq_rel_par' apply fastforce using Seq_rel_par' by fastforce

lemma rel_tran_par:
      "(((\<sigma>g,\<sigma>ls), (\<sigma>'g,\<sigma>'ls)), (\<Sigma>g, \<Sigma>ls), (\<Sigma>'g, \<Sigma>'ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow> i < length \<sigma>ls \<Longrightarrow>
         R_wf (length \<sigma>ls) \<alpha> \<Longrightarrow> R_wf (length \<sigma>ls) G\<^sub>c \<Longrightarrow> R_wf (length \<sigma>ls) G\<^sub>s \<Longrightarrow>
         length \<sigma>'ls = length \<sigma>ls \<Longrightarrow> length \<sigma>ls = length \<Sigma>ls \<Longrightarrow>  
         length \<Sigma>ls =  length \<Sigma>'ls \<Longrightarrow>  
          ((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>'g, \<sigma>'ls)), 
         (toSeqState i (\<Sigma>g, \<Sigma>ls), toSeqState i (\<Sigma>'g, \<Sigma>'ls))) \<in> 
           (Seq_rel i G\<^sub>c, (Seq_rel i G\<^sub>s)\<^sup>*)\<^sub>Seq_rel i \<alpha>"
  unfolding related_transitions_def 
  apply auto using par_rel_seq_rel apply fastforce using par_Seq_rel_tran_clor apply metis
  using par_rel_seq_rel apply fastforce using par_rel_seq_rel by fastforce 


lemma rel_tran_par':
      "(((\<sigma>g,\<sigma>ls), (\<sigma>'g,\<sigma>'ls)), (\<Sigma>g, \<Sigma>ls), (\<Sigma>'g, \<Sigma>'ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow> i < length \<sigma>ls \<Longrightarrow>
         Rel_wf i \<alpha> \<Longrightarrow> Rel_wf i G\<^sub>c \<Longrightarrow> Rel_wf i G\<^sub>s \<Longrightarrow>
         i<length \<sigma>'ls  \<Longrightarrow> i < length \<Sigma>ls \<Longrightarrow>  
         i < length \<Sigma>'ls \<Longrightarrow>  
          ((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>'g, \<sigma>'ls)), 
         (toSeqState i (\<Sigma>g, \<Sigma>ls), toSeqState i (\<Sigma>'g, \<Sigma>'ls))) \<in> 
           (Seq_rel i G\<^sub>c, (Seq_rel i G\<^sub>s)\<^sup>*)\<^sub>Seq_rel i \<alpha>"
  unfolding related_transitions_def 
  apply auto using par_rel_seq_rel' apply fast using par_Seq_rel_tran_clor' apply metis
  using par_rel_seq_rel' apply fastforce using par_rel_seq_rel' by fastforce 

lemma R_wf_to_Rel_fwf:"R_wf (Suc i) \<alpha> \<Longrightarrow> Rel_wf i \<alpha>"
  unfolding R_wf_def Rel_wf_def apply auto
  apply (metis (no_types) lessI)
  by (metis (no_types) lessI)

definition xx
  where "xx i Q \<equiv> Seq_rel i (Q !i)"


lemma "\<Sigma>ls \<noteq> [] \<Longrightarrow> ba \<noteq> [] \<Longrightarrow>
        drop (Suc 0) \<Sigma>ls = drop (Suc 0) ba \<Longrightarrow>  \<Sigma>ls ! 0 = ba ! 0 \<Longrightarrow> ba = \<Sigma>ls"
  by (metis SmallStepCon.nth_tl drop0 drop_Suc)
 
definition seq_rels
  where "seq_rels R = map (\<lambda>i. Seq_rel i (R!i)) [ 0..< (length R)]"

(* lemma "i\<le>length \<sigma>ls \<Longrightarrow> j\<le>length \<sigma>ls \<Longrightarrow> toParState i ((\<sigma>g,\<sigma>l), \<sigma>ls) = toParState j ((\<sigma>g,\<sigma>l),\<sigma>ls)"
  unfolding toParState_def Let_def split_def apply auto

lemma assumes a0:"i< length Rs" and a1:"j< length Rs" and
       a2:"\<forall>i< length Rs. Rel_wf k (Rs!i)" and a3:"i\<le>k" and a4:"j\<le> k" and a5:"h< length Rs"
     shows "Par_rel j ((seq_rels Rs)!h) = Par_rel i ((seq_rels Rs)!h)"
proof-
  have "(seq_rels Rs)!h = Seq_rel h (Rs!h)"
    unfolding seq_rels_def using a5  by auto
  
qed *)

lemma eq_length:"length Rls = length (seq_rels Rls)"
  unfolding seq_rels_def by auto

definition Rel_wf_seq::"nat \<Rightarrow> (('g1,'l1) c_state tran set) \<Rightarrow> bool"
  where "Rel_wf_seq i R \<equiv> \<forall>(x,y)\<in>R. i<length (snd x) \<and> i<length (snd y)"

lemma Rel_wf_seq1:"Rel_wf (i+1) R1 \<Longrightarrow> Rel_wf_seq i (Seq_rel i R1)"
  unfolding Rel_wf_def Rel_wf_seq_def Seq_rel_def toSeqState_def split_def by auto 

lemma Rel_wf_seq2:"Rel_wf_seq i (Seq_rel i R1) \<Longrightarrow> Rel_wf (i+1) R1"
  unfolding Rel_wf_def Rel_wf_seq_def Seq_rel_def toSeqState_def split_def  by auto 

lemma Rel_wf_seq:"Rel_wf_seq i (Seq_rel i R1) = Rel_wf (i+1) R1"
  using Rel_wf_seq1 Rel_wf_seq2 by auto

lemma Rel_wf_subset:"Rel_wf i R2 \<Longrightarrow> R1 \<subseteq> R2 \<Longrightarrow> Rel_wf i R1"
  unfolding Rel_wf_def by fastforce

lemma R_wf_subset:"R_wf i R2 \<Longrightarrow> R1 \<subseteq> R2 \<Longrightarrow> R_wf i R1"
  unfolding R_wf_def by fastforce

lemma Rel_wf_mon:"Rel_wf i R \<Longrightarrow> j\<le>i \<Longrightarrow> Rel_wf j R"
  unfolding Rel_wf_def by auto

lemma union_rel_wf:"length Rls - 1 \<le> i \<Longrightarrow> (\<Union>j<length Rls. (Rls !j)) \<subseteq> R \<Longrightarrow> 
       Rel_wf i R \<Longrightarrow> \<forall>i<length Rls. Rel_wf i (Rls!i)"
  apply auto 
  subgoal for j
      apply (rule Rel_wf_subset[of _ R], auto) 
      apply(cases "i=j", auto)
    by (rule Rel_wf_mon, auto)
  done


lemma rest_sim_1: assumes    
  a0:"G\<^sub>cj \<subseteq> R\<^sub>ci \<and> G\<^sub>sj \<subseteq> R\<^sub>si" and
  a0''':"k >0" and i_len:"i\<le>k" and  j_len:"j\<le>k" and ineqj:"i\<noteq>j" and   len_\<sigma>:"k < length \<sigma>ls" and 
  a5:" (\<Gamma>\<^sub>c, (C\<^sub>ci,toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i R\<^sub>ci, Seq_rel i G\<^sub>ci) 
           \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>Seq_rel i Q\<^sub>;\<^sub>Seq_rel i A\<^sub>) 
         (\<Gamma>\<^sub>s,(C\<^sub>si,toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i R\<^sub>si, Seq_rel i G\<^sub>si)" and       
   alpha_rel_guar:      " 
        ((toSeqState j (\<sigma>g, \<sigma>ls), toSeqState j (\<sigma>'g, (\<sigma>'ls))), 
           toSeqState j (\<Sigma>g, \<Sigma>ls), toSeqState j (\<Sigma>'g, \<Sigma>'ls)) 
             \<in> ((Seq_rel j G\<^sub>cj , (Seq_rel j G\<^sub>sj)\<^sup>*)\<^sub>(Seq_rel j \<alpha>))" and   
   a15:"Rel_wf k \<alpha>" and
   a18:"Rel_wf k G\<^sub>cj" and  a18':"Rel_wf k G\<^sub>sj" and  
   a19'':"Rel_wf k R\<^sub>ci" and  a19''':"Rel_wf k R\<^sub>si" and    
   len_\<Sigma>:"length \<Sigma>ls = length \<sigma>ls" and len_\<Sigma>':"length \<Sigma>ls = length \<Sigma>'ls" and 
   len_\<sigma>_\<sigma>':"length \<sigma>ls = length \<sigma>'ls" 
   shows "(\<Gamma>\<^sub>c,(C\<^sub>ci, toSeqState i (\<sigma>'g,\<sigma>'ls)), Seq_rel i R\<^sub>ci,Seq_rel i G\<^sub>ci) 
          \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>Seq_rel i Q\<^sub>;\<^sub>Seq_rel i A\<^sub>)
        (\<Gamma>\<^sub>s,(C\<^sub>si, toSeqState i (\<Sigma>'g, \<Sigma>'ls)), Seq_rel i R\<^sub>si,Seq_rel i G\<^sub>si)" 
proof-
  have rel_alpha:"((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>'g, (\<sigma>'ls))), 
                   toSeqState i (\<Sigma>g, \<Sigma>ls), toSeqState i (\<Sigma>'g, \<Sigma>'ls)) 
               \<in> ((Seq_rel i R\<^sub>ci, (Seq_rel i R\<^sub>si)\<^sup>*)\<^sub>(Seq_rel i \<alpha>))"
 proof- 
 { have x:
     "((toSeqState j (\<sigma>g, \<sigma>ls), toSeqState j (\<sigma>'g, (\<sigma>'ls))), 
        toSeqState j (\<Sigma>g, \<Sigma>ls), toSeqState j (\<Sigma>'g, \<Sigma>'ls)) 
        \<in> ((Seq_rel j G\<^sub>cj, (Seq_rel j G\<^sub>sj)\<^sup>*)\<^sub>(Seq_rel j \<alpha>))" 
     using alpha_rel_guar by auto    
   moreover  have 
     h:"(((\<sigma>g, \<sigma>ls), (\<sigma>'g, (\<sigma>'ls))), (\<Sigma>g, \<Sigma>ls),(\<Sigma>'g, \<Sigma>'ls)) \<in> (G\<^sub>cj, G\<^sub>sj\<^sup>*)\<^sub>\<alpha>"              
      using rel_tran_seq'[OF x] a15 a18 len_\<sigma>_\<sigma>'
            i_len len_\<Sigma> len_\<Sigma>' len_\<sigma> a0'''
      by (metis Rel_wf_mon a18' j_len le_less_trans)       
    have 
     "((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>'g, \<sigma>'ls)), 
       toSeqState i (\<Sigma>g, \<Sigma>ls), toSeqState i (\<Sigma>'g, \<Sigma>'ls))
        \<in> (Seq_rel i R\<^sub>ci, (Seq_rel i R\<^sub>si)\<^sup>*)\<^sub>Seq_rel i \<alpha>" 
      apply (rule rel_tran_par')
      using G_comp1[OF _ _ h, of "R\<^sub>ci" "R\<^sub>si"] a0
             apply auto
      using i_len le_less_trans len_\<sigma> 
      using Rel_wf_mon a15 i_len  a19'''  a19'' apply (blast, blast, blast, blast)
      using len_\<sigma>_\<sigma>' i_len le_less_trans len_\<sigma> len_\<Sigma> len_\<Sigma> len_\<Sigma>' by auto
    ultimately show ?thesis 
      by (meson a5 dest_sim_alpha env_sim)
  } qed          
  then have 
     "(\<Gamma>\<^sub>c,(C\<^sub>ci, toSeqState i (\<sigma>'g,\<sigma>'ls)), Seq_rel i R\<^sub>ci,Seq_rel i G\<^sub>ci) 
        \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>Seq_rel i Q\<^sub>;\<^sub>Seq_rel i A\<^sub>)
      (\<Gamma>\<^sub>s,(C\<^sub>si, toSeqState i (\<Sigma>'g, \<Sigma>'ls)), Seq_rel i R\<^sub>si,Seq_rel i G\<^sub>si)"           
     using  alpha_rel_guar step  
          sim_comp_not_mod[OF a5 rel_alpha] by auto
   thus ?thesis  by auto
 qed



lemma rest_sim: assumes    
  a0:"\<forall>i<length Rels\<^sub>c.
       R\<^sub>c \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. (Guas\<^sub>c ! j))
       \<subseteq> (Rels\<^sub>c ! i) \<and>
       R\<^sub>s \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. (Guas\<^sub>s ! j))
       \<subseteq> (Rels\<^sub>s!i)" and
    a0':"length Rels\<^sub>c = length Guas\<^sub>c \<and> length Rels\<^sub>c = length PostsQ \<and> length Rels\<^sub>c = length PostsA \<and>
         length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s " and
    a0''':"length Rels\<^sub>c >0" and
    a5:"\<forall>i<length PostsQ.                                                            
         (\<Gamma>\<^sub>c, (Coms\<^sub>c ! i,toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c !i), Seq_rel i (Guas\<^sub>c!i)) 
           \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>) 
         (\<Gamma>\<^sub>s,(Coms\<^sub>s! i,toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s!i), Seq_rel i (Guas\<^sub>s !i))" and
   a0'': "length Coms\<^sub>c = length Coms\<^sub>s" and
   a01'':"length Rels\<^sub>c = length Coms\<^sub>s" and      
   i_len:"i<length PostsQ" and  
   alpha_rel_guar:
      " (toSeqState i (\<sigma>'g, (\<sigma>'ls)), toSeqState i (\<Sigma>'g, \<Sigma>'ls)) \<in> Seq_rel i \<alpha> \<and>
        ((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>'g, (\<sigma>'ls))), 
           toSeqState i (\<Sigma>g, \<Sigma>ls), toSeqState i (\<Sigma>'g, \<Sigma>'ls)) 
             \<in> ((Seq_rel i (Guas\<^sub>c ! i), (Seq_rel i (Guas\<^sub>s ! i))\<^sup>*)\<^sub>(Seq_rel i \<alpha>)) \<and>
         (\<Gamma>\<^sub>c,(c', toSeqState i (\<sigma>'g, (\<sigma>'ls))), 
            Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
         (\<Gamma>\<^sub>s,(c\<^sub>s', toSeqState i (\<Sigma>'g, \<Sigma>'ls)),
             Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" and
   step:"i< length Coms\<^sub>c \<and>
        (\<forall>j. j\<noteq>i \<longrightarrow> Coms'\<^sub>c ! j = (Coms\<^sub>c !j)) \<and> Coms'\<^sub>c ! i= c' " and
   a15:"R_wf (length PostsQ) \<alpha>" and a16:"R_wf (length PostsQ) G\<^sub>c" and 
   a17:"R_wf (length PostsQ) G\<^sub>s" and a18:"\<forall>i<length PostsQ. R_wf (length PostsQ) (Guas\<^sub>c ! i)" and
   a19:"\<forall>i<length PostsQ. R_wf (length PostsQ) (Guas\<^sub>s ! i)" and 
   a20:"\<forall>i<length PostsQ. R_wf (length PostsQ) (Rels\<^sub>s ! i)" and
   a21:"\<forall>i<length PostsQ. R_wf (length PostsQ) (Rels\<^sub>c ! i)" and 
   len_\<sigma>:"length \<sigma>ls = length PostsQ" and "length \<sigma>ls = length \<sigma>'ls" and
   len_\<Sigma>:"length \<Sigma>ls = length \<sigma>ls" and len_\<Sigma>':"length \<Sigma>ls = length \<Sigma>'ls"
   shows "\<forall>i'<length PostsQ. (\<Gamma>\<^sub>c,(Coms'\<^sub>c ! i', toSeqState i' (\<sigma>'g,\<sigma>'ls)),
             Seq_rel i' (Rels\<^sub>c ! i'),Seq_rel i' (Guas\<^sub>c ! i')) 
          \<succeq>\<^sub>(\<^sub>Seq_rel i' \<alpha>\<^sub>;\<^sub>xx i' PostsQ\<^sub>;\<^sub>xx i' PostsA\<^sub>)
        (\<Gamma>\<^sub>s,(Coms\<^sub>s[i:=c\<^sub>s'] ! i', toSeqState i' (\<Sigma>'g, \<Sigma>'ls)),
            Seq_rel i' (Rels\<^sub>s ! i'),Seq_rel i' (Guas\<^sub>s ! i'))" 
proof-
 { fix i'
   assume i'_len:"i'<length PostsQ"
   { assume "i' = i" 
     then have 
       "(\<Gamma>\<^sub>c,(Coms'\<^sub>c ! i', toSeqState i' (\<sigma>'g, \<sigma>'ls)),Seq_rel i' (Rels\<^sub>c ! i'),Seq_rel i' (Guas\<^sub>c ! i'))
       \<succeq>\<^sub>(\<^sub>Seq_rel i' \<alpha>\<^sub>;\<^sub>xx i' PostsQ\<^sub>;\<^sub>xx i' PostsA\<^sub>)
    (\<Gamma>\<^sub>s,(Coms\<^sub>s[i := c\<^sub>s'] ! i', toSeqState i' (\<Sigma>'g, \<Sigma>'ls)),Seq_rel i' (Rels\<^sub>s ! i'),Seq_rel i' (Guas\<^sub>s ! i'))"
     using i'_len alpha_rel_guar step a0' a01'' by auto
   }
   moreover { assume i_i':"i'\<noteq>i"                  
     then have sim:
      "(\<Gamma>\<^sub>c, (Coms\<^sub>c ! i',toSeqState i' (\<sigma>g, \<sigma>ls)),Seq_rel i' (Rels\<^sub>c !i'), Seq_rel i' (Guas\<^sub>c!i')) 
         \<succeq>\<^sub>(\<^sub>Seq_rel i' \<alpha>\<^sub>;\<^sub>xx i' PostsQ\<^sub>;\<^sub>xx i' PostsA\<^sub>) 
       (\<Gamma>\<^sub>s,(Coms\<^sub>s! i',toSeqState i' (\<Sigma>g, \<Sigma>ls)),Seq_rel i' (Rels\<^sub>s!i'), Seq_rel i' (Guas\<^sub>s !i'))"
       using step a5 a0' a0'' a01'' i'_len by blast             
     have rel_alpha:"(toSeqState i' (\<sigma>'g, (\<sigma>'ls)), toSeqState i' (\<Sigma>'g, \<Sigma>'ls)) \<in> Seq_rel i' \<alpha> \<and>
                     ((toSeqState i' (\<sigma>g, \<sigma>ls), toSeqState i' (\<sigma>'g, (\<sigma>'ls))), 
                       toSeqState i' (\<Sigma>g, \<Sigma>ls), toSeqState i' (\<Sigma>'g, \<Sigma>'ls)) 
                   \<in> ((Seq_rel i' (Rels\<^sub>c ! i'), (Seq_rel i' (Rels\<^sub>s ! i'))\<^sup>*)\<^sub>(Seq_rel i' \<alpha>))" 
     proof- 
     {                 
       have x:
         "(toSeqState i (\<sigma>'g, (\<sigma>'ls)), toSeqState i (\<Sigma>'g, \<Sigma>'ls)) \<in> Seq_rel i \<alpha> \<and>
          ((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>'g, (\<sigma>'ls))), 
            toSeqState i (\<Sigma>g, \<Sigma>ls), toSeqState i (\<Sigma>'g, \<Sigma>'ls)) 
            \<in> ((Seq_rel i (Guas\<^sub>c ! i), (Seq_rel i (Guas\<^sub>s ! i))\<^sup>*)\<^sub>(Seq_rel i \<alpha>))" 
         using alpha_rel_guar by auto
       have "i' < length Rels\<^sub>c" using a0' i'_len by auto
       moreover have "i < length Guas\<^sub>c \<and> i < length Guas\<^sub>s" using a0' i_len by auto
       ultimately have "Guas\<^sub>c ! i \<subseteq> Rels\<^sub>c ! i' \<and> Guas\<^sub>s ! i \<subseteq> Rels\<^sub>s ! i'" 
         using a0 a01'' i_i' by blast 
       moreover  have 
         h:"(((\<sigma>g, \<sigma>ls), (\<sigma>'g, (\<sigma>'ls))), (\<Sigma>g, \<Sigma>ls),(\<Sigma>'g, \<Sigma>'ls)) \<in> (Guas\<^sub>c ! i, (Guas\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha>"              
          using rel_tran_seq[OF conjunct2[OF x]] a15 a18 
              a19 assms(18) i_len len_\<Sigma> len_\<Sigma>' len_\<sigma> by presburger              
        then have 
          h:"(((\<sigma>g, \<sigma>ls), (\<sigma>'g, (\<sigma>'ls))), (\<Sigma>g, \<Sigma>ls),(\<Sigma>'g, \<Sigma>'ls)) \<in> (Rels\<^sub>c ! i', (Rels\<^sub>s ! i')\<^sup>*)\<^sub>\<alpha>"
          using G_comp1[OF _ _ h, of "Rels\<^sub>c ! i'" "Rels\<^sub>s ! i'"] calculation
          by auto
       thus ?thesis using rel_tran_par[OF h]
         by (metis \<open>i' < length Rels\<^sub>c\<close> a0' a15 a20 a21 assms(18) 
               dest_sim_alpha env_sim len_\<Sigma> len_\<Sigma>' len_\<sigma> sim) 
     } qed                 
     have "(\<Gamma>\<^sub>c,(Coms'\<^sub>c ! i', toSeqState i' (\<sigma>'g, (\<sigma>'ls))), Seq_rel i' (Rels\<^sub>c ! i'),Seq_rel i' (Guas\<^sub>c ! i'))
          \<succeq>\<^sub>(\<^sub>Seq_rel i' \<alpha>\<^sub>;\<^sub>xx i' PostsQ\<^sub>;\<^sub>xx i' PostsA\<^sub>)
        (\<Gamma>\<^sub>s,(Coms\<^sub>s[i:=c\<^sub>s'] ! i', toSeqState i' (\<Sigma>'g, \<Sigma>'ls)), Seq_rel i' (Rels\<^sub>s ! i'),Seq_rel i' (Guas\<^sub>s ! i'))"          
       using i_i' alpha_rel_guar step  
            sim_comp_not_mod[OF sim conjunct2[OF rel_alpha]] by auto
   }
   ultimately have 
    "(\<Gamma>\<^sub>c,(Coms'\<^sub>c ! i', toSeqState i' (\<sigma>'g, \<sigma>'ls)),Seq_rel i' (Rels\<^sub>c ! i'),Seq_rel i' (Guas\<^sub>c ! i'))
       \<succeq>\<^sub>(\<^sub>Seq_rel i' \<alpha>\<^sub>;\<^sub>xx i' PostsQ\<^sub>;\<^sub>xx i' PostsA\<^sub>)
    (\<Gamma>\<^sub>s,(Coms\<^sub>s[i := c\<^sub>s'] ! i', toSeqState i' (\<Sigma>'g, \<Sigma>'ls)),Seq_rel i' (Rels\<^sub>s ! i'),Seq_rel i' (Guas\<^sub>s ! i'))"
      using i_len i'_len  by fastforce        
 } thus  ?thesis by auto
qed 

    
(* lemma par_all_skip_rtran:
    "\<forall>i<length C. \<Gamma>\<turnstile>\<^sub>c (C!i, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, s) \<Longrightarrow> length C > 0 \<Longrightarrow>
       \<exists>C'. \<Gamma>\<turnstile>\<^sub>p (C,s) \<rightarrow>\<^sub>\<tau>\<^sup>* (C', s) \<and> (\<forall>i<length C'. C' ! i = Skip) \<and> C' \<noteq> []"
proof (induction C )
  case (Nil) thus ?case by auto
next
  case (Cons a as)   
  {assume a0:"as=Nil"    
   then have "\<Gamma>\<turnstile>\<^sub>p (a#as, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (a#as[0:=Skip],s)" 
     using  Cons(2) mult_step_in_par by auto
   then have ?case using a0
     by (metis Cons.prems(1) length_Cons length_list_update less_Suc0 list.discI list.size(3) 
               list_update.simps(1) mult_step_in_par nth_list_update_eq) 
  }
  moreover { fix a1 as1
    assume a0:"as=a1#as1"
    then have "\<forall>i<length (as). \<Gamma>\<turnstile>\<^sub>c (as ! i, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, s)" 
      using Cons by auto
    moreover have "0 < length as" using a0 by auto
    ultimately obtain c'' where 
     x:"\<Gamma>\<turnstile>\<^sub>p (as, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c'',s) \<and> (\<forall>i<length c''. c'' ! i = LanguageCon.com.Skip) \<and> c'' \<noteq> []"
      using Cons(1) by auto
    then have "\<Gamma>\<turnstile>\<^sub>p (a#as, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (a#c'', s)" using par_tran_comp_rtran by auto
    moreover have step_c:"\<Gamma>\<turnstile>\<^sub>c ((a # c'') ! 0, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, s)" using Cons by auto
    ultimately have "\<Gamma>\<turnstile>\<^sub>p (a # as, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip#c'', s)" 
      using ParComp[of 0 "a#c''"] rtranclp.simps
    proof -
      have "\<Gamma>\<turnstile>\<^sub>p (a # c'',s) \<rightarrow>\<^sub>\<tau>\<^sup>* ((a # c'')[0 := LanguageCon.com.Skip], s)"
        using step_c mult_step_in_par by blast
      then show ?thesis
        using \<open>\<Gamma>\<turnstile>\<^sub>p (a # as, s) \<rightarrow>\<^sub>\<tau>\<^sup>* (a # c'',s)\<close> by fastforce
    qed 
    then have ?case using x
      by (metis (no_types, lifting) length_Cons less_Suc_eq_0_disj list.discI nth_Cons_0 nth_Cons_Suc)  
  }      
  ultimately show ?case
    using list.exhaust by blast
      
qed *)

  
lemma aaa:"Suc i< length a \<Longrightarrow> Suc i< length b \<Longrightarrow> Suc i< length c \<Longrightarrow> Suc i<length d \<Longrightarrow> 
Suc i< length e \<Longrightarrow> Suc i< length f \<Longrightarrow> Suc i< length g \<Longrightarrow> Suc i<length h \<Longrightarrow> 
P (a!(Suc i)) (b!(Suc i)) (c!(Suc i)) (d!(Suc i)) (e!(Suc i)) (f!(Suc i)) (g!(Suc i)) (h!(Suc i)) \<Longrightarrow> 
P ((drop 1 a) !i) ((drop 1 b) !i) ((drop 1 c) !i) ((drop 1 d) !i) ((drop 1 e) !i) ((drop 1 f) !i) ((drop 1 g) !i) ((drop 1 h) !i)"  
  by fastforce  

lemma bbb:"length a = length b \<and> length a = length c \<and> length a = length d \<and>
           length a = length e \<and> length a = length f \<and> length a = length g \<and>
           length a = length h \<Longrightarrow>
          Suc i<length a \<Longrightarrow> P (a!(Suc i)) (b!(Suc i)) (c!(Suc i)) (d!(Suc i)) (e!(Suc i)) (f!(Suc i)) (g!(Suc i)) (h!(Suc i)) \<Longrightarrow> 
          P ((drop 1 a) !i) ((drop 1 b) !i) ((drop 1 c) !i) ((drop 1 d) !i) ((drop 1 e) !i) ((drop 1 f) !i) ((drop 1 g) !i) ((drop 1 h) !i)"
  using aaa by auto
  
lemma ccc:
assumes a0:"length a = length b \<and> length a = length c \<and> length a = length d \<and>
           length a = length e \<and> length a = length f \<and> length a = length g \<and>
           length a = length h" and
        a1:"\<forall>i<length a.   P (a!i) (b!i) (c!i) (d!i) (e!i) (f!i) (g!i) (h!i)"
      shows  "\<forall>i<length (drop 1 a). P ((drop 1 a) !i) ((drop 1 b) !i) ((drop 1 c) !i) ((drop 1 d) !i) ((drop 1 e) !i) ((drop 1 f) !i) ((drop 1 g) !i) ((drop 1 h) !i)"
proof -
  {fix i
  assume a3:"i<length (drop 1 a)"
  then have a4:"Suc i < length a" by auto
  then have a5:" P (a!Suc i) (b!Suc i) (c!Suc i) (d!Suc i) (e!Suc i) (f!Suc i) (g!Suc i) (h!Suc i)" 
    using a1 by auto
  then have "P ((drop 1 a) !i) ((drop 1 b) !i) ((drop 1 c) !i) ((drop 1 d) !i) ((drop 1 e) !i) ((drop 1 f) !i) ((drop 1 g) !i) ((drop 1 h) !i)"   
    using bbb[OF a0 a4] by auto
 }thus ?thesis by auto
qed
 
  
(* lemma x1:"\<forall>i<length C\<^sub>s'. C\<^sub>s'!i = Skip \<Longrightarrow> i< length ((Ca # C\<^sub>s')[0 := LanguageCon.com.Skip] ) \<Longrightarrow>
           (Ca # C\<^sub>s')[0 := LanguageCon.com.Skip] ! i = LanguageCon.com.Skip"
  sorry *)
  
lemma  G_in_R_drop:
  assumes a0:"\<forall>i<length R. A \<union> (\<Union>a\<in>{j. j < length G \<and> j \<noteq> i}. G ! a) \<subseteq> R ! i" and
          a1:"length R>0" and a2:"length G=length R"
  shows"\<forall>i<length (drop 1 R). 
        A \<union> (\<Union>a\<in>{j. j < length (drop 1 G) \<and> j \<noteq> i}. 
                   (drop 1 G) ! a) \<subseteq> (drop 1 R) ! i"        
  proof-
  {fix i
    assume len:"i<length (drop 1 R)"             
    then have r1:       
    "A \<union> (\<Union>a\<in>{j. j < length G \<and> j \<noteq> (Suc i)}. G ! a) \<subseteq> R ! (Suc i)"
      using a0 by auto
    have "(\<Union>a\<in>{j. j < length (drop 1 G) \<and> j \<noteq> i}. (drop 1 G) ! a) \<union> G ! 0 = 
         (\<Union>a\<in>{j. j < length G \<and> j \<noteq> (Suc i)}. G ! a) "          
    proof- 
      { fix x
        assume a0:"x \<in> ((\<Union>a\<in>{j. j < length (drop 1 G) \<and> j \<noteq> i}. (drop 1 G) ! a) \<union> G ! 0)"                       
        then have "x\<in>(\<Union>a\<in>{j. j < length G \<and> j \<noteq> (Suc i)}. G ! a)"
          using a0 a1 a2
          apply auto 
          apply (subgoal_tac "Suc xa<length G") 
            by auto               
      }
      moreover 
      {fix x
        fix j
        assume a00: "j < length G" and
               a01:"j \<noteq> Suc i" and
               a02:"x\<in>G !j"
        then have "(\<exists>j. j<length (drop 1 G) \<and> j\<noteq>i \<and> x\<in>(drop 1 G) ! j) \<or> x \<in>G ! 0"             
        proof-
          { assume a03:"j=0"
            then have ?thesis using a00 a01 a02 by auto
          }
          moreover {
            assume a03:"j\<noteq>0"            
            then obtain j' where suc: "j = Suc j'" 
              using not_gr_zero gr0_implies_Suc by auto
            then have "j'<length G - Suc 0 \<and> j' \<noteq> i \<and> x \<in> drop (Suc 0) G ! j'"
              using a00 a01 a02  by auto                      
            then have ?thesis using a00 a01 a02  by auto
          }
          ultimately show ?thesis by auto
        qed
        then have "x \<in> ((\<Union>a\<in>{j. j < length (drop 1 G) \<and> j \<noteq> i}. (drop 1 G)!a) \<union> G ! 0)"
          by auto             
      }              
      ultimately show ?thesis by fast qed
    then have "(\<Union>a\<in>{j. j < length (drop 1 G) \<and> j \<noteq> i}. (drop 1 G) ! a) \<subseteq> 
               (\<Union>a\<in>{j. j < length G \<and> j \<noteq> (Suc i)}. G ! a)"
      by auto
    then have "A \<union> (\<Union>a\<in>{j. j < length (drop 1 G) \<and> j \<noteq> i}. (drop 1 G) ! a) \<subseteq> (drop 1 R) ! i"
      using r1 len by auto          
  } thus ?thesis by fastforce
  qed   

lemma tran_Guar:
  assumes 
          a1:"0 < length (Ca # Cs)" and          
          a3:"length (Ca # Cs) = length C\<^sub>c \<and> length (Ca # Cs) = length Rels\<^sub>c" and
          a4:"length Rels\<^sub>c = length Guas\<^sub>c \<and>
              length Rels\<^sub>c = length PostsQ \<and>
              length Rels\<^sub>c = length PostsA \<and> length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s" and
           a5:"(((\<sigma>, \<sigma>),(\<Sigma>1, \<Sigma>2)) \<in> (Guas\<^sub>c!0,(Guas\<^sub>s!0)\<^sup>*)\<^sub>\<alpha>)" and
           a6:"Guasc = drop 1 Guas\<^sub>c \<and> Guass = drop 1 Guas\<^sub>s \<and> Postsq = drop 1 PostsQ \<and> 
             Postsa = drop 1 PostsA \<and> Csc = drop 1 C\<^sub>c" and
           a7:"(( \<sigma>,  \<sigma>), \<Sigma>, \<Sigma>1) \<in> 
                 (((\<Union>j<length Guasc. (Guasc !j)), (\<Union>j<length Guass. (Guass !j))\<^sup>*)\<^sub>\<alpha>) \<and>                   
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Cs,\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s', \<Sigma>1)"
    shows "((\<sigma>, \<sigma>), \<Sigma>, \<Sigma>2) \<in> 
            (((\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)), (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s !j))\<^sup>*)\<^sub>\<alpha>)"
proof-
  have len:"0<length Guas\<^sub>s" using a7 a1 a3 a4 by auto
  then have f1:"((\<sigma>, \<sigma>), \<Sigma>, \<Sigma>2) \<in> 
          (((\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)), ((\<Union>j<length Guass. (Guass !j))\<union>(Guas\<^sub>s!0) )\<^sup>*)\<^sub>\<alpha>)"
  using a4 a7 a6 a5 a3  unfolding related_transitions_def
  apply auto   by (meson in_rtrancl_UnI rtrancl_trans)
  then have "(\<Union>j<length Guass. (Guass !j))\<union>(Guas\<^sub>s!0) \<subseteq>(\<Union>j<length Guas\<^sub>s. Guas\<^sub>s ! j)"
  using a6 len by fastforce
    thus ?thesis using  G_comp1[OF _ _ f1] by auto  
  qed
    
lemma guar_i_rely_j:
  assumes 
     a0:"0<length PostsQ" and
     a1:"length Rels\<^sub>c = length Guas\<^sub>c \<and>
        length Rels\<^sub>c = length PostsQ \<and>
        length Rels\<^sub>c = length PostsA \<and> length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s" and
     a2:"\<forall>i<length Rels\<^sub>c. R\<^sub>c \<union> (\<Union>a\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. Guas\<^sub>c ! a) \<subseteq> Rels\<^sub>c ! i" and
     a3:"\<forall>i<length Rels\<^sub>s. R\<^sub>s \<union> (\<Union>a\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. Guas\<^sub>s ! a) \<subseteq> Rels\<^sub>s ! i" and
     a4:"(((\<sigma>, \<sigma>),(\<Sigma>, \<Sigma>')) \<in> (Guas\<^sub>c!0,(Guas\<^sub>s!0)\<^sup>*)\<^sub>\<alpha>)"             
    shows "\<forall>i<length Guas\<^sub>c. i\<noteq>0 \<longrightarrow> (((\<sigma>, \<sigma>), \<Sigma>, \<Sigma>') \<in> (Rels\<^sub>c ! i, (Rels\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha>) "
      
proof-
  have inguars:"\<forall>i<length Rels\<^sub>c. i\<noteq>0 \<longrightarrow> Guas\<^sub>c!0 \<subseteq> Rels\<^sub>c!i \<and> Guas\<^sub>s!0 \<subseteq> Rels\<^sub>s!i"
  proof-
    {fix i
      assume a00:"i<length Rels\<^sub>c"  and a01:"i\<noteq>0"        
      have lens:"i<length Rels\<^sub>s" using a00 a1 by auto
      also have "0<length Guas\<^sub>c \<and> 0<length Guas\<^sub>s" using a0 a1 by auto
      ultimately have "Guas\<^sub>c!0 \<subseteq> Rels\<^sub>c!i \<and> Guas\<^sub>s!0 \<subseteq> Rels\<^sub>s!i" using a00 a01 a2 a3 a0 a1 
      by blast        
    }thus ?thesis by auto    
  qed
  then show ?thesis
  proof-
    {fix i
    assume a00:"i<length Guas\<^sub>c" and a01:"i\<noteq>0"
    then have "i<length Rels\<^sub>c" using a00 a1 by auto
    then have "Guas\<^sub>c!0 \<subseteq> Rels\<^sub>c!i \<and> Guas\<^sub>s!0 \<subseteq> Rels\<^sub>s!i" using a01 inguars by fastforce
    then have "(((\<sigma>, \<sigma>), \<Sigma>, \<Sigma>') \<in> (Rels\<^sub>c ! i, (Rels\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha>)"
      using G_comp1 a4 by auto }
    thus ?thesis by auto
  qed    
qed

lemma guar_i_rely_j':
  assumes      
     a1:"length Rels\<^sub>c = length Guas\<^sub>c \<and>
         length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s" and
     a2:"\<forall>i<length Rels\<^sub>c. R\<^sub>c \<union> (\<Union>a\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. Guas\<^sub>c ! a) \<subseteq> Rels\<^sub>c ! i" and
     a3:"\<forall>i<length Rels\<^sub>s. R\<^sub>s \<union> (\<Union>a\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. Guas\<^sub>s ! a) \<subseteq> Rels\<^sub>s ! i" and     
     a4:"((\<sigma>, \<sigma>),(\<Sigma>, \<Sigma>')) \<in> (\<Union> ((!) Guas\<^sub>c ` {i. i\<noteq>j \<and> i<length Guas\<^sub>c}), (\<Union> ((!) Guas\<^sub>s ` {i. i\<noteq>j \<and> i<length Guas\<^sub>s}))\<^sup>*)\<^sub>\<alpha>" and 
     a5:"j < length Rels\<^sub>c" 
    shows "(((\<sigma>, \<sigma>), \<Sigma>, \<Sigma>') \<in> (Rels\<^sub>c ! j, (Rels\<^sub>s ! j)\<^sup>*)\<^sub>\<alpha>) "
      
proof-
  have inguars:"\<forall>i<length Guas\<^sub>c. i\<noteq>j \<longrightarrow> Guas\<^sub>c!i \<subseteq> Rels\<^sub>c!j \<and> Guas\<^sub>s!i \<subseteq> Rels\<^sub>s!j"
  proof-
    {fix i
      assume a00:"i<length Guas\<^sub>c"  and a01:"i\<noteq>j"        
      have lens:"i<length Rels\<^sub>s" using a00 a1 by auto
      also have "i<length Guas\<^sub>s" using  a1 a00 by auto
      ultimately have "Guas\<^sub>c!i \<subseteq> Rels\<^sub>c!j \<and> Guas\<^sub>s!i \<subseteq> Rels\<^sub>s!j" using a00 a01 a2 a3 a1 a5 
        apply auto
        by blast 
    }thus ?thesis by auto    
  qed
  then show ?thesis
  proof-    
    have "j<length Rels\<^sub>c" and "j<length Rels\<^sub>s" using a1 a5 by auto          
    have "(\<Union> ((!) Guas\<^sub>c ` {i. i\<noteq>j \<and> i<length Guas\<^sub>c})) \<subseteq> Rels\<^sub>c!j"           
      using a2   a1 a5 by auto           
    moreover have "(\<Union> ((!) Guas\<^sub>s ` {i. i\<noteq>j \<and> i<length Guas\<^sub>s})) \<subseteq> Rels\<^sub>s!j"
      using a2   a1 a5 apply auto
        by (metis  inguars   subsetD)    
    ultimately have "(((\<sigma>, \<sigma>), \<Sigma>, \<Sigma>') \<in> (Rels\<^sub>c ! j, (Rels\<^sub>s ! j)\<^sup>*)\<^sub>\<alpha>)"
      using G_comp1 a4 by auto 
    thus ?thesis by auto
  qed    
qed
  
lemma guars_i_rels_0:
  assumes a0:"Cs=Ca1#Cs1" and       
          a1:"0 < length (Ca # Cs)" and 
          a2:"length (Ca # Cs) = length C\<^sub>c \<and> length (Ca # Cs) = length Rels\<^sub>c" and
          a3:"length Rels\<^sub>c = length Guas\<^sub>c \<and>
              length Rels\<^sub>c = length PostsQ \<and>
              length Rels\<^sub>c = length PostsA \<and>
              length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s" and
          a4:"\<forall>i<length Rels\<^sub>c.
       R\<^sub>c \<union> (\<Union>a\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. Guas\<^sub>c ! a) \<subseteq> Rels\<^sub>c ! i" and
          a5:"\<forall>i<length Rels\<^sub>s.
       R\<^sub>s \<union> (\<Union>a\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. Guas\<^sub>s ! a) \<subseteq> Rels\<^sub>s ! i" and
          a6:"((\<sigma>, \<sigma>), s\<^sub>s, ns1) \<in> 
                 (((\<Union>j<length (drop 1 Guas\<^sub>c). ((drop 1 Guas\<^sub>c) !j)), (\<Union>j<length (drop 1 Guas\<^sub>s). ((drop 1 Guas\<^sub>s) !j))\<^sup>*)\<^sub>\<alpha>)"
  shows "((\<sigma>, \<sigma>), s\<^sub>s,  ns1) \<in> (Rels\<^sub>c!0, (Rels\<^sub>s!0)\<^sup>*)\<^sub>\<alpha>"  
proof-
    let ?Guasc = "(drop 1 Guas\<^sub>c)"
    let ?Guass = "(drop 1 Guas\<^sub>s)"
    have "length Guas\<^sub>c > Suc 0" using a0 a1 a2 a3 by auto
    then have guasc_sub:"(\<Union>j<length ?Guasc. (?Guasc !j)) \<subseteq> (\<Union>x\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> 0}. Guas\<^sub>c ! x)"
      using Suc_less_eq2 by fastforce
    have "length Rels\<^sub>c > 0" using a1 a2 by auto
    then have "R\<^sub>c \<union> (\<Union>x\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> 0}. Guas\<^sub>c ! x) \<subseteq> Rels\<^sub>c ! 0" 
      using  a4 by auto
    then have a00:"(\<Union>j<length ?Guasc. (?Guasc !j)) \<subseteq> Rels\<^sub>c!0"
      using guasc_sub by blast
    have "length Guas\<^sub>s > Suc 0" using a0 a1 a2 a3 by auto
    then have guass_sub:"(\<Union>j<length ?Guass. (?Guass !j)) \<subseteq> (\<Union>x\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> 0}. Guas\<^sub>s ! x)"
      using Suc_less_eq2 by fastforce
    have "length Rels\<^sub>s > 0" using a0 a1 a2 a3 by auto
    then have "R\<^sub>s \<union> (\<Union>x\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> 0}. Guas\<^sub>s ! x) \<subseteq> Rels\<^sub>s ! 0" 
      using  a5 by auto
    then have a1:"(\<Union>j<length ?Guass. (?Guass !j)) \<subseteq> Rels\<^sub>s!0"
      using guass_sub by blast 
    show ?thesis using a6 G_comp1[OF a00 a1] by auto
  qed        
  

lemma eq_length_pev_step':"\<Gamma>\<turnstile>\<^sub>p\<^sub>e (S , \<Sigma>g, \<Sigma>ls) \<rightarrow> (S', \<Sigma>g', \<Sigma>ls') \<Longrightarrow>
        length \<Sigma>ls = length \<Sigma>ls'"
  using eq_length_p_step' steppe_stepp by fastforce


lemma eq_length_pev_tran_step':"\<Gamma>\<turnstile>\<^sub>p (S , \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S', \<Sigma>g', \<Sigma>ls') \<Longrightarrow> 
       length \<Sigma>ls = length \<Sigma>ls'"  
  using p_step_local_length by fastforce


lemma sim_final:
  assumes 
  a2:"(\<Gamma>\<^sub>c,(x, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i R\<^sub>c,Seq_rel i G\<^sub>c)
       \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>Seq_rel i Q\<^sub>;\<^sub>Seq_rel i A\<^sub>) 
      (\<Gamma>\<^sub>s,(S ! i, toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i R\<^sub>s,Seq_rel i G\<^sub>s)" and   
  a1:"x=Skip \<or> x = Throw \<or> (\<exists>f. x = Fault f) \<or> x = Stuck" and
  a3:"((\<sigma>g, \<sigma>ls), \<Sigma>g, \<Sigma>ls) \<in> \<alpha>" and
  a4:" length \<sigma>ls = length \<Sigma>ls" and   
  a5:"Sim_Rules.Rel_wf i Q" and a5':"Sim_Rules.Rel_wf i A" and
  a8:"Rel_wf i \<alpha>" and a9:"Rel_wf i GC" and 
  a10:"Rel_wf i GS" and
  a11:" G\<^sub>c \<subseteq> GC" and 
  a12:"G\<^sub>s \<subseteq> GS" and a13:"i < length \<sigma>ls" and  a14:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and 
  a15:"i<length S" and a16:"length S \<le> length \<sigma>ls"
shows  "\<exists>ab bb y.
          (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> ((GC, GS\<^sup>*)\<^sub>\<alpha>) \<and>
          (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S , \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[i:=y], ab, bb)) \<and> 
          ((x = Skip \<and> y = Skip \<and> ((\<sigma>g, \<sigma>ls), ab, bb) \<in> Q) \<or> 
           (x = Throw \<and> y = Throw \<and> ((\<sigma>g, \<sigma>ls), ab, bb) \<in> A) \<or> 
           (\<exists>f. x = Fault f \<and>  y = Fault f) \<or> (x = Stuck \<and> y = Stuck))"
proof-
  have len_\<sigma>:"i<length \<sigma>ls" and  len_\<Sigma>:"i<length \<Sigma>ls" using a8
    using Rel_wf_def   a4  a13 by fastforce+  
  have a18:" Rel_wf i G\<^sub>c" and 
       a19:"Rel_wf i G\<^sub>s" 
    using Rel_wf_subset[OF a9 a11] Rel_wf_subset[OF a10 a12]
    by auto 
  then  have 
    "\<exists>\<Sigma>g' \<Sigma>l' y. ((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>g, \<sigma>ls)), 
       toSeqState i (\<Sigma>g, \<Sigma>ls), ((\<Sigma>g', \<Sigma>l'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))))
        \<in> (Seq_rel i G\<^sub>c, (Seq_rel i G\<^sub>s)\<^sup>*)\<^sub>Seq_rel i \<alpha> \<and>
        \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S ! i, CRef.toSeq (toSeqState i (\<Sigma>g, \<Sigma>ls))) \<rightarrow>\<^sub>\<tau>\<^sup>* (y, (\<Sigma>g', \<Sigma>l')) \<and>
     ((x = Skip \<and> y = Skip \<and> (toSeqState i (\<sigma>g, \<sigma>ls), ((\<Sigma>g', \<Sigma>l'),snd (toSeqState i (\<Sigma>g, \<Sigma>ls)))) \<in> Seq_rel i Q) \<or> 
      (x = Throw \<and> y = Throw  \<and> (toSeqState i (\<sigma>g, \<sigma>ls), ((\<Sigma>g', \<Sigma>l'),snd (toSeqState i (\<Sigma>g, \<Sigma>ls)))) \<in> Seq_rel i A) \<or> 
           (\<exists>f. x = Fault f \<and>  y = Fault f) \<or> (x = Stuck \<and> y = Stuck))"
    using a1 a2  apply (cases x, auto) 
      apply (frule dest_final_skip, auto simp add: toSeq_def)     
      apply (frule dest_final_Stuck, auto simp add: toSeq_def)     
      apply (frule dest_final_Fault, auto simp add: toSeq_def) 
    by (frule dest_final_Throw, auto simp add: toSeq_def) 
  then obtain \<Sigma>g' \<Sigma>l' y where step: "((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>g, \<sigma>ls)), 
       toSeqState i (\<Sigma>g, \<Sigma>ls), ((\<Sigma>g', \<Sigma>l'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))))
        \<in> (Seq_rel i G\<^sub>c, (Seq_rel i G\<^sub>s)\<^sup>*)\<^sub>Seq_rel i \<alpha> \<and>
        \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S ! i, CRef.toSeq (toSeqState i (\<Sigma>g, \<Sigma>ls))) \<rightarrow>\<^sub>\<tau>\<^sup>* (y, (\<Sigma>g', \<Sigma>l')) \<and>
        ((x = Skip \<and> y = Skip \<and> 
            (toSeqState i (\<sigma>g, \<sigma>ls), ((\<Sigma>g', \<Sigma>l'),snd (toSeqState i (\<Sigma>g, \<Sigma>ls)))) \<in> Seq_rel i Q) \<or> 
         (x = Throw \<and> y = Throw \<and> 
            (toSeqState i (\<sigma>g, \<sigma>ls), ((\<Sigma>g', \<Sigma>l'),snd (toSeqState i (\<Sigma>g, \<Sigma>ls)))) \<in> Seq_rel i A)  \<or> 
         (\<exists>f. x = Fault f \<and>  y = Fault f) \<or> (x = Stuck \<and> y = Stuck))" 
    by auto
  have eq_\<Sigma>:"((\<Sigma>g', \<Sigma>l'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))) = 
          toSeqState i ( toParState i ((\<Sigma>g', \<Sigma>l'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))))"
    using a13 a4 Par2Seq0
    by (simp add: Par2Seq0 len_toSeqState)
  have len_\<Sigma>':"i<length (snd ( toParState i ((\<Sigma>g', \<Sigma>l'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls)))))" 
    using len_\<sigma> len_\<Sigma>
    unfolding toSeqState_def toParState_def by simp    
  obtain \<Sigma>lls' where 
      eq_seq:"(\<Sigma>g', \<Sigma>lls') = toParState i ((\<Sigma>g', \<Sigma>l'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))) \<and>
              ((\<Sigma>g', \<Sigma>l'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))) = toSeqState i (\<Sigma>g', \<Sigma>lls')" 
    using toPar_gi eq_\<Sigma>
    by (metis (no_types, lifting) prod.exhaust_sel)  
  have eq_to_seq:"toParState i ((\<Sigma>g', \<Sigma>l'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))) = 
                  toPar i (\<Sigma>g', \<Sigma>l') (\<Sigma>g, \<Sigma>ls)" 
     unfolding toParState_def toSeqState_def Let_def split_def apply auto
     by (simp add: len_\<Sigma> less_imp_le_nat min.absorb2 upd_conv_take_nth_drop)
  have rel:"(((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), (\<Sigma>g', \<Sigma>lls')) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
  proof-    
    have rel:"((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>g, \<sigma>ls)), 
           toSeqState i (\<Sigma>g, \<Sigma>ls), toSeqState i (\<Sigma>g', \<Sigma>lls'))
            \<in> (Seq_rel i G\<^sub>c, (Seq_rel i G\<^sub>s)\<^sup>*)\<^sub>Seq_rel i \<alpha>" 
      using   eq_seq local.step   by force      
    have a6':"Rel_wf 0 \<alpha>" using a8  unfolding Rel_wf_def by auto    
    show ?thesis using rel_tran_seq'[OF rel len_\<sigma> a8 a18 a19 len_\<sigma> len_\<sigma> len_\<Sigma>] a4  a18 a19 
               eq_seq  len_\<Sigma>'
      by (metis  snd_conv)      
  qed
  then have "(((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), (\<Sigma>g', \<Sigma>lls')) \<in> (GC, GS\<^sup>*)\<^sub>\<alpha> \<and> 
              (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), (\<Sigma>g', \<Sigma>lls')) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
  proof-    
     have a1:"G\<^sub>c \<subseteq> GC" and a2:"G\<^sub>s \<subseteq> GS" using a11 a12 by blast+
    then show ?thesis using rel G_comp1[OF a1 a2 rel]  by auto
  qed  
  moreover have "\<gamma>\<^sub>n \<subseteq> \<alpha>" using a14 by auto
  moreover have "x = Skip \<and> y = Skip \<and> ((\<sigma>g, \<sigma>ls), \<Sigma>g', \<Sigma>lls') \<in>  Q \<or> 
                 x = Throw \<and> y = Throw \<and> ((\<sigma>g, \<sigma>ls), \<Sigma>g', \<Sigma>lls') \<in>  A \<or> 
               (\<exists>f. x = Fault f \<and>  y = Fault f) \<or> (x = Stuck \<and> y = Stuck)"
  proof-
    { assume a00:"x = Skip"
      then have "(toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<Sigma>g', \<Sigma>lls')) \<in> Seq_rel i Q" 
        using eq_seq step unfolding xx_def by force    
      then have "x = Skip \<and> y = Skip \<and> ((\<sigma>g, \<sigma>ls), \<Sigma>g', \<Sigma>lls') \<in>  Q"     
        using Seq_rel_par'     eq_seq len_\<Sigma>' len_\<sigma> a5 LanguageCon.com.simps(25) LanguageCon.com.simps(31) 
                LanguageCon.com.simps(33)
        by (metis  a00 local.step snd_conv)
    }  
    moreover { assume a00:"x = Throw" 
      then have "(toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<Sigma>g', \<Sigma>lls')) \<in> Seq_rel i A" 
        using eq_seq step unfolding xx_def by force    
      then have "x = Throw \<and> y = Throw \<and> ((\<sigma>g, \<sigma>ls), \<Sigma>g', \<Sigma>lls') \<in>  A"     
        using Seq_rel_par'     eq_seq len_\<Sigma>' len_\<sigma> a5' a00 step 
          LanguageCon.com.simps(32)
        by (metis LanguageCon.com.distinct(147) LanguageCon.com.simps(183) snd_conv)
    }
    moreover { assume a00:"(\<exists>f. x = Fault f)"      
      then have "\<exists>f. x = Fault f \<and> y = Fault f" using step by auto
    }
    moreover { assume a00:"x = Stuck" 
      then have "x = Stuck \<and> y = Stuck" using step by simp
    }
    ultimately show ?thesis using a1 by auto
  qed
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[i:=y], (\<Sigma>g', \<Sigma>lls')) \<and> 
                ((x = Skip \<and> y = Skip) \<or> (x = Throw \<and> y = Throw) \<or> 
                (\<exists>f. x = Fault f \<and>  y = Fault f) \<or> (x = Stuck \<and> y = Stuck))" 
  proof-
    have step_par_s:
      "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[i:=y], toPar i (\<Sigma>g', \<Sigma>l') (\<Sigma>g, \<Sigma>ls))"      
    proof- 
       have f3:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S ! i, toSeqPar i (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (y, (\<Sigma>g', \<Sigma>l'))" 
        using step  
        by (auto simp add: toSeqPar_toSeq_SeqState)  
      then show ?thesis using mult_step_in_par1[OF _ _ f3] 
        using a15 a16 by (simp add: a4)      
    qed
    then show ?thesis  
      using eq_to_seq eq_seq using step by metis      
  qed    
  ultimately show ?thesis by auto 
qed       

lemma sim_final_i:assumes 
  a2:"(\<Gamma>\<^sub>c,(Skip, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i R\<^sub>c,Seq_rel i G\<^sub>c)
       \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>Seq_rel i Q\<^sub>;\<^sub>Seq_rel i A\<^sub>) 
      (\<Gamma>\<^sub>s,(S ! i, toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i R\<^sub>s,Seq_rel i G\<^sub>s)" and   
  a3:"((\<sigma>g, \<sigma>ls), \<Sigma>g, \<Sigma>ls) \<in> \<alpha>" and
  a4:" length \<sigma>ls = length \<Sigma>ls" and   
  a5:"Sim_Rules.Rel_wf i Q" and
  a8:"Rel_wf i \<alpha>" and a9:"Rel_wf i GC" and 
  a10:"Rel_wf i GS" and
  a11:" G\<^sub>c \<subseteq> GC" and 
  a12:"G\<^sub>s \<subseteq> GS" and a13:"i < length \<sigma>ls" and  a14:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and 
  a15:"i<length S" and a16:"length S \<le> length \<sigma>ls"
shows  "\<exists>ab bb.
          (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> ((GC, GS\<^sup>*)\<^sub>\<alpha>) \<and>
          (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          ((\<sigma>g, \<sigma>ls), ab, bb) \<in> Q \<and>
          \<gamma>\<^sub>n \<subseteq> \<alpha> \<and> (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S , \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[i:=Skip], ab, bb))"
proof-
  have len_\<sigma>:"i<length \<sigma>ls" and  len_\<Sigma>:"i<length \<Sigma>ls" using a8
    using Rel_wf_def   a4  a13 by fastforce+  
  have a18:" Rel_wf i G\<^sub>c" and 
       a19:"Rel_wf i G\<^sub>s" 
    using Rel_wf_subset[OF a9 a11] Rel_wf_subset[OF a10 a12]
    by auto 
  note x =  dest_final_skip[OF a2] 
  then obtain  \<Sigma>g' \<Sigma>l'  where step:
    "((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>g, \<sigma>ls)), 
       toSeqState i (\<Sigma>g, \<Sigma>ls), ((\<Sigma>g', \<Sigma>l'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))))
        \<in> (Seq_rel i G\<^sub>c, (Seq_rel i G\<^sub>s)\<^sup>*)\<^sub>Seq_rel i \<alpha> \<and>         
        (toSeqState i (\<sigma>g, \<sigma>ls), ((\<Sigma>g', \<Sigma>l'),snd (toSeqState i (\<Sigma>g, \<Sigma>ls)))) \<in> Seq_rel i Q \<and>       
        \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S ! i, CRef.toSeq (toSeqState i (\<Sigma>g, \<Sigma>ls))) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, (\<Sigma>g', \<Sigma>l'))"
     unfolding toSeq_def by auto     
  have eq_\<Sigma>:"((\<Sigma>g', \<Sigma>l'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))) = 
          toSeqState i ( toParState i ((\<Sigma>g', \<Sigma>l'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))))"
    using a13 a4 Par2Seq0
    by (simp add: Par2Seq0 len_toSeqState)
  have len_\<Sigma>':"i<length (snd ( toParState i ((\<Sigma>g', \<Sigma>l'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls)))))" 
    using len_\<sigma> len_\<Sigma>
    unfolding toSeqState_def toParState_def by simp    
  obtain \<Sigma>lls' where 
      eq_seq:"(\<Sigma>g', \<Sigma>lls') = toParState i ((\<Sigma>g', \<Sigma>l'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))) \<and>
              ((\<Sigma>g', \<Sigma>l'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))) = toSeqState i (\<Sigma>g', \<Sigma>lls')" 
    using toPar_gi eq_\<Sigma>
    by (metis (no_types, lifting) prod.exhaust_sel)  
  have eq_to_seq:"toParState i ((\<Sigma>g', \<Sigma>l'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))) = 
                  toPar i (\<Sigma>g', \<Sigma>l') (\<Sigma>g, \<Sigma>ls)" 
     unfolding toParState_def toSeqState_def Let_def split_def apply auto
     by (simp add: len_\<Sigma> less_imp_le_nat min.absorb2 upd_conv_take_nth_drop)
  have rel:"(((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), (\<Sigma>g', \<Sigma>lls')) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
  proof-    
    have rel:"((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>g, \<sigma>ls)), 
           toSeqState i (\<Sigma>g, \<Sigma>ls), toSeqState i (\<Sigma>g', \<Sigma>lls'))
            \<in> (Seq_rel i G\<^sub>c, (Seq_rel i G\<^sub>s)\<^sup>*)\<^sub>Seq_rel i \<alpha>" 
      using   eq_seq local.step   by force      
    have a6':"Rel_wf 0 \<alpha>" using a8  unfolding Rel_wf_def by auto    
    show ?thesis using rel_tran_seq'[OF rel len_\<sigma> a8 a18 a19 len_\<sigma> len_\<sigma> len_\<Sigma>] a4  a18 a19 
               eq_seq  len_\<Sigma>'
      by (metis  snd_conv)      
  qed
  then have "(((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), (\<Sigma>g', \<Sigma>lls')) \<in> (GC, GS\<^sup>*)\<^sub>\<alpha> \<and> 
              (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), (\<Sigma>g', \<Sigma>lls')) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
  proof-    
     have a1:"G\<^sub>c \<subseteq> GC" and a2:"G\<^sub>s \<subseteq> GS" using a11 a12 by blast+
    then show ?thesis using rel G_comp1[OF a1 a2 rel]  by auto
  qed    
  moreover have "((\<sigma>g, \<sigma>ls), \<Sigma>g', \<Sigma>lls') \<in>  Q"
  proof-
    have "(toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<Sigma>g', \<Sigma>lls')) \<in> Seq_rel i Q" 
      using eq_seq step unfolding xx_def by force    
    then show ?thesis 
      using Seq_rel_par'     eq_seq
      by (metis len_\<Sigma>' len_\<sigma> a5 snd_conv)  
  qed  
  moreover have "\<gamma>\<^sub>n \<subseteq> \<alpha>" using a14 by auto
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[i:=Skip], (\<Sigma>g', \<Sigma>lls'))" 
  proof-
    have step_par_s:
      "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[i:=Skip], toPar i (\<Sigma>g', \<Sigma>l') (\<Sigma>g, \<Sigma>ls))"      
    proof- 
       have f3:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S ! i, toSeqPar i (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, (\<Sigma>g', \<Sigma>l'))" 
        using step  
        by (auto simp add: toSeqPar_toSeq_SeqState)  
      then show ?thesis using mult_step_in_par1[OF _ _ f3] 
        using a15 a16 by (simp add: a4)      
    qed
    then show ?thesis  
      using eq_to_seq eq_seq 
      by presburger      
  qed    
  ultimately show ?thesis by auto 
qed       


lemma sim_final_i_throw:assumes 
  a2:"(\<Gamma>\<^sub>c,(Throw, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i R\<^sub>c,Seq_rel i G\<^sub>c)
       \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>Seq_rel i Q\<^sub>;\<^sub>Seq_rel i A\<^sub>) 
      (\<Gamma>\<^sub>s,(S ! i, toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i R\<^sub>s,Seq_rel i G\<^sub>s)" and   
  a3:"((\<sigma>g, \<sigma>ls), \<Sigma>g, \<Sigma>ls) \<in> \<alpha>" and
  a4:" length \<sigma>ls = length \<Sigma>ls" and   
  a5:"Sim_Rules.Rel_wf i A" and
  a8:"Rel_wf i \<alpha>" and a9:"Rel_wf i GC" and 
  a10:"Rel_wf i GS" and
  a11:" G\<^sub>c \<subseteq> GC" and 
  a12:"G\<^sub>s \<subseteq> GS" and a13:"i < length \<sigma>ls" and  a14:"\<gamma>\<^sub>a \<subseteq> \<alpha>" and 
  a15:"i<length S" and a16:"length S \<le> length \<sigma>ls"
shows  "\<exists>ab bb.
          (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> ((GC, GS\<^sup>*)\<^sub>\<alpha>) \<and>
          (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          ((\<sigma>g, \<sigma>ls), ab, bb) \<in> A \<and>
          \<gamma>\<^sub>a \<subseteq> \<alpha> \<and> (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S , \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[i:=Throw], ab, bb))"
proof-
  have len_\<sigma>:"i<length \<sigma>ls" and  len_\<Sigma>:"i<length \<Sigma>ls" using a8
    using Rel_wf_def   a4  a13 by fastforce+  
  have a18:" Rel_wf i G\<^sub>c" and 
       a19:"Rel_wf i G\<^sub>s" 
    using Rel_wf_subset[OF a9 a11] Rel_wf_subset[OF a10 a12]
    by auto 
  note x =  dest_final_Throw[OF a2] 
  then obtain  \<Sigma>g' \<Sigma>l'  where step:
    "((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>g, \<sigma>ls)), 
       toSeqState i (\<Sigma>g, \<Sigma>ls), ((\<Sigma>g', \<Sigma>l'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))))
        \<in> (Seq_rel i G\<^sub>c, (Seq_rel i G\<^sub>s)\<^sup>*)\<^sub>Seq_rel i \<alpha> \<and>         
        (toSeqState i (\<sigma>g, \<sigma>ls), ((\<Sigma>g', \<Sigma>l'),snd (toSeqState i (\<Sigma>g, \<Sigma>ls)))) \<in> Seq_rel i A \<and>
        Seq_rel i A \<subseteq> Seq_rel i \<alpha> \<and>
        \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S ! i, CRef.toSeq (toSeqState i (\<Sigma>g, \<Sigma>ls))) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Throw, (\<Sigma>g', \<Sigma>l'))"
     unfolding toSeq_def by auto     
  have eq_\<Sigma>:"((\<Sigma>g', \<Sigma>l'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))) = 
          toSeqState i ( toParState i ((\<Sigma>g', \<Sigma>l'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))))"
    using a13 a4 Par2Seq0
    by (simp add: Par2Seq0 len_toSeqState)
  have len_\<Sigma>':"i<length (snd ( toParState i ((\<Sigma>g', \<Sigma>l'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls)))))" 
    using len_\<sigma> len_\<Sigma>
    unfolding toSeqState_def toParState_def by simp    
  obtain \<Sigma>lls' where 
      eq_seq:"(\<Sigma>g', \<Sigma>lls') = toParState i ((\<Sigma>g', \<Sigma>l'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))) \<and>
              ((\<Sigma>g', \<Sigma>l'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))) = toSeqState i (\<Sigma>g', \<Sigma>lls')" 
    using toPar_gi eq_\<Sigma>
    by (metis (no_types, lifting) prod.exhaust_sel)  
  have eq_to_seq:"toParState i ((\<Sigma>g', \<Sigma>l'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))) = 
                  toPar i (\<Sigma>g', \<Sigma>l') (\<Sigma>g, \<Sigma>ls)" 
     unfolding toParState_def toSeqState_def Let_def split_def apply auto
     by (simp add: len_\<Sigma> less_imp_le_nat min.absorb2 upd_conv_take_nth_drop)
  have rel:"(((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), (\<Sigma>g', \<Sigma>lls')) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
  proof-    
    have rel:"((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>g, \<sigma>ls)), 
           toSeqState i (\<Sigma>g, \<Sigma>ls), toSeqState i (\<Sigma>g', \<Sigma>lls'))
            \<in> (Seq_rel i G\<^sub>c, (Seq_rel i G\<^sub>s)\<^sup>*)\<^sub>Seq_rel i \<alpha>" 
      using   eq_seq local.step   by force      
    have a6':"Rel_wf 0 \<alpha>" using a8  unfolding Rel_wf_def by auto    
    show ?thesis using rel_tran_seq'[OF rel len_\<sigma> a8 a18 a19 len_\<sigma> len_\<sigma> len_\<Sigma>] a4  a18 a19 
               eq_seq  len_\<Sigma>'
      by (metis  snd_conv)      
  qed
  then have "(((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), (\<Sigma>g', \<Sigma>lls')) \<in> (GC, GS\<^sup>*)\<^sub>\<alpha> \<and> 
              (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), (\<Sigma>g', \<Sigma>lls')) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
  proof-    
     have a1:"G\<^sub>c \<subseteq> GC" and a2:"G\<^sub>s \<subseteq> GS" using a11 a12 by blast+
    then show ?thesis using rel G_comp1[OF a1 a2 rel]  by auto
  qed    
  moreover have "((\<sigma>g, \<sigma>ls), \<Sigma>g', \<Sigma>lls') \<in>  A"
  proof-
    have "(toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<Sigma>g', \<Sigma>lls')) \<in> Seq_rel i A" 
      using eq_seq step unfolding xx_def by force    
    then show ?thesis 
      using Seq_rel_par'     eq_seq
      by (metis len_\<Sigma>' len_\<sigma> a5 snd_conv)  
  qed  
  moreover have "\<gamma>\<^sub>a \<subseteq> \<alpha>" using a14 by auto
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[i:=Throw], (\<Sigma>g', \<Sigma>lls'))" 
  proof-
    have step_par_s:
      "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[i:=Throw], toPar i (\<Sigma>g', \<Sigma>l') (\<Sigma>g, \<Sigma>ls))"      
    proof- 
       have f3:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S ! i, toSeqPar i (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, (\<Sigma>g', \<Sigma>l'))" 
        using step  
        by (auto simp add: toSeqPar_toSeq_SeqState)  
      then show ?thesis using mult_step_in_par1[OF _ _ f3] 
        using a15 a16 by (simp add: a4)      
    qed
    then show ?thesis  
      using eq_to_seq eq_seq 
      by presburger      
  qed    
  ultimately show ?thesis by auto 
qed



lemma sim_final_1:assumes 
  a0':"length Rels\<^sub>c = length Guas\<^sub>c \<and>
         length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s " and
  a1:" \<forall>i<length [x]. [x] ! i = LanguageCon.com.Skip" and
  a2:"\<forall>i<length [x]. (\<Gamma>\<^sub>c,([x] ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
       \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i Q\<^sub>;\<^sub>xx i A\<^sub>) (\<Gamma>\<^sub>s,(S ! i, toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" and   
  a3:"((\<sigma>g, \<sigma>ls), \<Sigma>g, \<Sigma>ls) \<in> \<alpha>" and
  a4:" length \<sigma>ls = length \<Sigma>ls" and   
  a5:" \<forall>i<length Q. Sim_Rules.Rel_wf i (Q ! i)" and
  a6: "0 < length Q" and 
  a7:"length A = length Q \<and> length Q = length S \<and> 
      length Q = length [x] \<and> length [x] \<le> length Rels\<^sub>c" and
  a8:"Rel_wf  ((length Rels\<^sub>c)-1) \<alpha>" and a9:"Rel_wf ((length Rels\<^sub>c)-1) G\<^sub>c" and 
  a10:"Rel_wf ((length Rels\<^sub>c)-1) G\<^sub>s" and
  a11:" (\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)) \<subseteq> G\<^sub>c" and
  a12:" (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s ! j)) \<subseteq> G\<^sub>s" and a13:"length Rels\<^sub>c = length \<sigma>ls" and  a14:"\<gamma>\<^sub>n \<subseteq> \<alpha>" 
shows  "\<exists>ab bb.
          (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
          (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> 
              ((\<Union>j<length Q. (Guas\<^sub>c !j)), (\<Union>j<length Q. (Guas\<^sub>s ! j))\<^sup>*)\<^sub>\<alpha> \<and>
          ((\<sigma>g, \<sigma>ls), ab, bb) \<in> \<Inter> ((!) Q ` {..<length Q}) \<and>
          \<gamma>\<^sub>n \<subseteq> \<alpha> \<and> (\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', ab, bb) \<and> 
         (\<forall>i<length c\<^sub>s'. c\<^sub>s' ! i = LanguageCon.com.Skip) \<and> c\<^sub>s' \<noteq> [])"
proof-
  have sim:"(\<Gamma>\<^sub>c,(Skip, toSeqState 0 (\<sigma>g, \<sigma>ls)),Seq_rel 0 (Rels\<^sub>c ! 0),Seq_rel 0 (Guas\<^sub>c ! 0))
       \<succeq>\<^sub>(\<^sub>Seq_rel 0 \<alpha>\<^sub>;\<^sub>xx 0 Q\<^sub>;\<^sub>xx 0 A\<^sub>)
       (\<Gamma>\<^sub>s,(S ! 0, toSeqState 0 (\<Sigma>g, \<Sigma>ls)),Seq_rel 0 (Rels\<^sub>s ! 0),Seq_rel 0 (Guas\<^sub>s ! 0))"
    using a1 a2 by auto     
   have "\<exists>ab bb.
         (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
         (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> ((Guas\<^sub>c ! 0), ((Guas\<^sub>s ! 0))\<^sup>*)\<^sub>\<alpha> \<and>
         ((\<sigma>g, \<sigma>ls), ab, bb) \<in> Q ! 0 \<and>
         \<gamma>\<^sub>n \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[0 := LanguageCon.com.Skip], ab, bb)"    
     using a5 a6 a8 a9 a10 
     apply clarify  
     apply (rule sim_final_i[OF sim[simplified xx_def] a3 a4, of G\<^sub>c G\<^sub>s \<gamma>\<^sub>n])
     using a5 a6  apply fastforce 
     using  Rel_wf_mon apply (fastforce, fastforce, fastforce)
     using a0' a7  a11 a12 a13 a14 by fastforce+  
   moreover have "\<Inter> ((!) Q ` {..<length Q}) = Q ! 0" using a6 a7 apply auto
     using less_Suc0 by force
   moreover have "S[0:=Skip] = [Skip]"
     by (metis (no_types) a7 length_0_conv length_Cons list.exhaust list_update_code(2) nat.inject)
   moreover have "(\<Union>j<length Q. (Guas\<^sub>c !j)) = Guas\<^sub>c!0" 
     using a6 a7 apply auto using less_Suc0 by force
   moreover have "(\<Union>j<length Q. (Guas\<^sub>s !j)) = Guas\<^sub>s!0" 
     using a6 a7 apply auto using less_Suc0 by force
   ultimately show ?thesis by fastforce 
 qed

lemma sim_final_throw_1:assumes 
  a0':"length Rels\<^sub>c = length Guas\<^sub>c \<and>
         length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s " and
  a1:" \<forall>i<length [x]. [x] ! i = Throw" and
  a2:"\<forall>i<length [x]. (\<Gamma>\<^sub>c,([x] ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
       \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i Q\<^sub>;\<^sub>xx i A\<^sub>) (\<Gamma>\<^sub>s,(S ! i, toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" and   
  a3:"((\<sigma>g, \<sigma>ls), \<Sigma>g, \<Sigma>ls) \<in> \<alpha>" and
  a4:" length \<sigma>ls = length \<Sigma>ls" and   
  a5:" \<forall>i<length Q. Sim_Rules.Rel_wf i (A ! i)" and
  a6: "0 < length Q" and 
  a7:"length A = length Q \<and> length Q = length S \<and> 
      length Q = length [x] \<and> length [x] \<le> length Rels\<^sub>c" and
  a8:"Rel_wf  ((length Rels\<^sub>c)-1) \<alpha>" and a9:"Rel_wf ((length Rels\<^sub>c)-1) G\<^sub>c" and 
  a10:"Rel_wf ((length Rels\<^sub>c)-1) G\<^sub>s" and
  a11:" (\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)) \<subseteq> G\<^sub>c" and
  a12:" (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s ! j)) \<subseteq> G\<^sub>s" and a13:"length Rels\<^sub>c = length \<sigma>ls" and  a14:"\<gamma>\<^sub>a \<subseteq> \<alpha>" 
shows  "\<exists>ab bb.
          (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
          (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> 
              ((\<Union>j<length Q. (Guas\<^sub>c !j)), (\<Union>j<length Q. (Guas\<^sub>s ! j))\<^sup>*)\<^sub>\<alpha> \<and>
          ((\<sigma>g, \<sigma>ls), ab, bb) \<in> \<Union> ((!) A ` {..<length A}) \<and>
          \<gamma>\<^sub>a \<subseteq> \<alpha> \<and> (\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', ab, bb) \<and> throw_program c\<^sub>s')"
proof-
  have sim:"(\<Gamma>\<^sub>c,(Throw, toSeqState 0 (\<sigma>g, \<sigma>ls)),Seq_rel 0 (Rels\<^sub>c ! 0),Seq_rel 0 (Guas\<^sub>c ! 0))
       \<succeq>\<^sub>(\<^sub>Seq_rel 0 \<alpha>\<^sub>;\<^sub>xx 0 Q\<^sub>;\<^sub>xx 0 A\<^sub>)
       (\<Gamma>\<^sub>s,(S ! 0, toSeqState 0 (\<Sigma>g, \<Sigma>ls)),Seq_rel 0 (Rels\<^sub>s ! 0),Seq_rel 0 (Guas\<^sub>s ! 0))"
    using a1 a2 by auto     
   have "\<exists>ab bb.
         (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
         (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> ((Guas\<^sub>c ! 0), ((Guas\<^sub>s ! 0))\<^sup>*)\<^sub>\<alpha> \<and>
         ((\<sigma>g, \<sigma>ls), ab, bb) \<in> A ! 0 \<and>
         \<gamma>\<^sub>a \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[0 := Throw], ab, bb)"    
     using a5 a6 a8 a9 a10 
     apply clarify  
     apply (rule sim_final_i_throw[OF sim[simplified xx_def] a3 a4, of G\<^sub>c G\<^sub>s \<gamma>\<^sub>a])
     using a5 a6  apply fastforce 
     using  Rel_wf_mon apply (fastforce, fastforce, fastforce)
     using a0' a7  a11 a12 a13 a14 by fastforce+  
   moreover have "\<Union> ((!) A ` {..<length A}) = A ! 0" using a6 a7 apply auto
     using less_Suc0 by force
   moreover have "S[0:=Throw] = [Throw]"
     by (metis (no_types) a7 length_0_conv length_Cons list.exhaust list_update_code(2) nat.inject)
   then have "throw_program (S[0 := Throw])" unfolding throw_program_def by auto
   moreover have "(\<Union>j<length Q. (Guas\<^sub>c !j)) = Guas\<^sub>c!0" 
     using a6 a7 apply auto using less_Suc0 by force
   moreover have "(\<Union>j<length Q. (Guas\<^sub>s !j)) = Guas\<^sub>s!0" 
     using a6 a7 apply auto using less_Suc0 by force
   ultimately show ?thesis by fastforce 
 qed

lemma concat_prog_par_stepl:
  assumes a0:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>\<tau> (s, \<Sigma>) \<rightarrow> (s', \<Sigma>')"
  shows"\<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>\<tau> (s@rs, \<Sigma>) \<rightarrow> (s'@rs, \<Sigma>')"
proof-
  obtain i r \<Sigma>a' where step:"i < length s \<and> 
             \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (s ! i, fst \<Sigma>, snd \<Sigma> ! i) \<rightarrow> (r, \<Sigma>a') \<and> s' = s[i := r] \<and>
             \<Sigma>' = (fst \<Sigma>a', (snd \<Sigma>)[i := snd \<Sigma>a'])"     
    using a0 by (fastforce elim: step_pev_pair_elim_cases)
  moreover have "s!i = (s@rs)!i" using calculation
    by (simp add: l_append local.step) 
  ultimately have 
     cond: "i< length (s@rs) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> ((s@rs)! i, fst \<Sigma>, snd \<Sigma> ! i) \<rightarrow> (r, \<Sigma>a') \<and> (s'@rs) = (s@rs)[i := r] \<and>
      \<Sigma>' = (fst \<Sigma>a', (snd \<Sigma>)[i := snd \<Sigma>a'])"
    using list_update_append1 by fastforce 
  then show ?thesis 
    by (metis ParCompe getList.simps toPar.simps toSeqPar.simps)
qed

lemma take_tran_clos_stepl:
     "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>) \<rightarrow>\<^sup>+ (S', \<Sigma>') \<Longrightarrow>
     \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S@rs, \<Sigma>) \<rightarrow>\<^sup>+ (S'@ rs, \<Sigma>')"
proof (induct arbitrary:  rule:Transitive_Closure.tranclp_induct2[case_names Refl Step])
  case (Refl s \<Sigma>') then show ?case
    by (simp add: concat_prog_par_stepl tranclp.r_into_trancl) 
next
  case (Step s \<Sigma>1 s' \<Sigma>')
  then show ?case using concat_prog_par_stepl
    by (metis (no_types, hide_lams) tranclp.trancl_into_trancl)
qed


lemma take_refl_tran_clos_stepl:
      "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S', \<Sigma>g', \<Sigma>ls') \<Longrightarrow>          
       \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S@rs, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S'@rs, \<Sigma>g', \<Sigma>ls')"
  apply (erule converse_rtranclpE2)
  apply force
  by (meson rtranclp_into_tranclp2 take_tran_clos_stepl tranclp_into_rtranclp)   

lemma take_refl_tran_clos_step:
      "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S@rs, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S@rs', \<Sigma>g', \<Sigma>ls') \<Longrightarrow>
       \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g', \<Sigma>ls') \<rightarrow>\<^sub>\<tau>\<^sup>* (S', \<Sigma>g'', \<Sigma>ls'') \<Longrightarrow>          
       \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S@rs, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S'@rs', \<Sigma>g'', \<Sigma>ls'')"
  using  take_refl_tran_clos_stepl
proof -
  assume a1: "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g', \<Sigma>ls') \<rightarrow>\<^sub>\<tau>\<^sup>* (S', \<Sigma>g'', \<Sigma>ls'')"
  assume a2: "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S@rs, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S@rs', \<Sigma>g', \<Sigma>ls')"
  then show ?thesis 
    using a1 by (meson rtranclp_trans take_refl_tran_clos_stepl)
qed 

lemma take_refl_tran_clos_step':
  assumes a0:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (take n S@rs', \<Sigma>g', \<Sigma>ls')" and
        a1:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (take n S, \<Sigma>g', \<Sigma>ls') \<rightarrow>\<^sub>\<tau>\<^sup>* (RS', \<Sigma>g'', \<Sigma>ls'')" 
      shows "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (RS'@rs', \<Sigma>g'', \<Sigma>ls'')"
proof-
  have S:"S = take n S@drop n S" by auto
  then have a0:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (take n S@drop n S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (take n S@rs', \<Sigma>g', \<Sigma>ls')" 
    using a0 by auto
  thus ?thesis using take_refl_tran_clos_step[OF a0 a1] by auto
qed 


lemma tran_step_par_same_len_program:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (S', (\<Sigma>g', \<Sigma>ls')) \<Longrightarrow>
      length S = length S'"
proof (induct  rule:rtranclp_induct2[case_names Refl Step])
  case Refl
  then show ?case by auto
next
  case (Step S' \<Sigma>' S'' \<Sigma>'')
  then show ?case
    using dest_par_step by fastforce
qed
  

lemma take_concat:
  "take (length S) (S@rs) = S" 
  by auto

lemma "A\<subseteq>B \<Longrightarrow> A\<^sup>* \<subseteq> B\<^sup>*"
  using Transitive_Closure.rtrancl_mono by auto

lemma "j< length Guas\<^sub>s \<Longrightarrow>
       \<Union> ((!) Guas\<^sub>s ` {..<j})\<subseteq> \<Union> ((!) Guas\<^sub>s ` {i. i \<noteq> j \<and> i < length Guas\<^sub>s})"
  by auto

lemma sim_i:
  assumes  
    step:"(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)\<and> 
         (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> 
            ((Guas\<^sub>c ! (length (xs @ [x]) - 1)), ((Guas\<^sub>s ! (length (xs @ [x]) - 1)))\<^sup>*)\<^sub>\<alpha> " and
    a0:"\<forall>i<length (xs @ [x]). 
         (\<Gamma>\<^sub>c,((xs @ [x]) ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
             \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i Q\<^sub>;\<^sub>xx i A\<^sub>) 
         (\<Gamma>\<^sub>s,(S ! i, toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" and
    a1:"length Rels\<^sub>c = length Guas\<^sub>c \<and>
         length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s " and 
    a2:"length A = length Q \<and> length Q = length S \<and> 
        length Q = length (xs @ [x]) \<and> length (xs @ [x]) \<le> length Rels\<^sub>c" and
    a3:"\<forall>i<length Rels\<^sub>c.
          R\<^sub>c \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. (Guas\<^sub>c ! j)) \<subseteq> (Rels\<^sub>c ! i) \<and>
          R\<^sub>s \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. (Guas\<^sub>s ! j)) \<subseteq> (Rels\<^sub>s!i)" and
    a4:" (\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)) \<subseteq> G\<^sub>c" and
    a5:" (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s ! j)) \<subseteq> G\<^sub>s" and a6:"xs\<noteq>[]" and a7:"length \<sigma>ls = length \<Sigma>ls" and 
    a8:"length Rels\<^sub>c = length \<sigma>ls" and 
    a9:"Rel_wf  ((length Rels\<^sub>c)-1) \<alpha>" and a10:"Rel_wf ((length Rels\<^sub>c)-1) G\<^sub>c" and 
    a11:"Rel_wf ((length Rels\<^sub>c)-1) G\<^sub>s" and 
    a12:"\<forall>i<length Rels\<^sub>c. Rel_wf ((length Rels\<^sub>c)-1) (Rels\<^sub>s ! i)" and
    a13:"\<forall>i<length Rels\<^sub>c. Rel_wf ((length Rels\<^sub>c)-1) (Rels\<^sub>c ! i)" and a14:"length \<Sigma>ls = length \<Sigma>ls'"
  shows "\<forall>i<length xs.
       (\<Gamma>\<^sub>c,(xs ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
         \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i Q\<^sub>;\<^sub>xx i A\<^sub>)
       (\<Gamma>\<^sub>s,(S ! i, toSeqState i (\<Sigma>g', \<Sigma>ls')),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))"
proof- 
  let ?i = "length (xs@[x]) - 1"
  let ?Q = "take (length xs) Q"
  let ?A = "take (length xs) A" 
  let ?S = "take (length xs) S"
  { fix i
    assume a00:"i<length xs" 
    then have a00':"i<?i" by auto
    have sim:"(\<Gamma>\<^sub>c,(xs ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
         \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i Q\<^sub>;\<^sub>xx i A\<^sub>)
       (\<Gamma>\<^sub>s,(S ! i, toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))"  
    proof-
    {
      have "xs!i = (xs@[x])!i" and a00':"i<length (xs@[x])"
        using a00 by (auto simp add: l_append)
      moreover have "?Q!i = Q!i" using a00 by auto
      moreover have "?A!i = A!i" using a00 by auto
      moreover have "?S!i = S!i" using a00 by auto
      moreover note mp[OF spec[OF a0, of i] a00']
      ultimately have "(\<Gamma>\<^sub>c,(xs ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
          \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i Q\<^sub>;\<^sub>xx i A\<^sub>)
          (\<Gamma>\<^sub>s,(S ! i, toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))"
        unfolding xx_def by auto 
    } thus ?thesis by auto qed  
    have gc_rs1:"Guas\<^sub>c ! (length (xs @ [x]) - 1) \<subseteq> Rels\<^sub>c ! i" 
    proof-      
      have "length (xs @ [x]) - 1 < length Guas\<^sub>c" using a1 a2 by auto
      moreover have "i< length (xs @ [x])" using a00 by auto
      then have  " \<Union> ((!) Guas\<^sub>c ` {j. j < length Guas\<^sub>c \<and> j \<noteq> i}) \<subseteq> Rels\<^sub>c ! i" 
        using  a1 a2 a3  by auto
      moreover have "?i\<noteq>i" using a00 by auto
      ultimately show  ?thesis  by auto
    qed
    have gc_rs2:"Guas\<^sub>s ! (length (xs @ [x]) - 1) \<subseteq> Rels\<^sub>s ! i" 
    proof-      
      have "length (xs @ [x]) - 1 < length Guas\<^sub>s" using a1 a2 by auto
      moreover have "i< length (xs @ [x])" using a00 by auto
      then have  " \<Union> ((!) Guas\<^sub>s ` {j. j < length Guas\<^sub>s \<and> j \<noteq> i}) \<subseteq> Rels\<^sub>s ! i" 
        using  a1 a2 a3 by auto
      moreover have "?i\<noteq>i" using a00 by auto
      ultimately show  ?thesis  by auto
    qed
    have gc_gc:"Guas\<^sub>c ! length xs \<subseteq> G\<^sub>c"
    proof-
     have "length xs < length Guas\<^sub>c" using a1 a2 by auto      
     then show  ?thesis using a4 by auto
    qed
    have gs_gs:"Guas\<^sub>s ! length xs \<subseteq> G\<^sub>s"
    proof-
      have "length xs < length Guas\<^sub>s" using a1 a2 by auto      
      then show  ?thesis using a5 by auto
    qed
    have "(\<Gamma>\<^sub>c,(xs ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
         \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i Q\<^sub>;\<^sub>xx i A\<^sub>)
       (\<Gamma>\<^sub>s,(S ! i, toSeqState i (\<Sigma>g', \<Sigma>ls')),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))"
      unfolding xx_def
      apply (rule rest_sim_1[of "(Guas\<^sub>c ! ?i)" "(Rels\<^sub>c ! i)" "(Guas\<^sub>s ! ?i)" "(Rels\<^sub>s ! i)" ?i i ?i \<sigma>ls \<Gamma>\<^sub>c 
                           "xs!i" \<sigma>g "(Guas\<^sub>c ! i)" \<alpha> "Q!i" "A!i" \<Gamma>\<^sub>s "S!i" \<Sigma>g \<Sigma>ls "(Guas\<^sub>s ! i)"])
                          apply auto using gc_rs1 gc_rs2 apply auto[2] using a6 apply auto[1] 
      using a00 apply auto[2] using a2 a1 a7 a8 apply auto[1] 
      using sim[simplified xx_def] apply auto[1]      
                   apply (rule rel_tran_par', insert step, simp) 
      using a2 a1 a8 apply simp
      using a2  apply (fastforce intro:Rel_wf_mon[OF a9])
                       apply (rule Rel_wf_subset[of _ G\<^sub>c])  
      using a2  apply (fastforce intro:Rel_wf_mon[OF a10])      
      using gc_gc apply auto[1]
                       apply (rule Rel_wf_subset[of _ G\<^sub>s])  
      using a2  apply (fastforce intro:Rel_wf_mon[OF a11])      
      using gs_gs apply auto[1]
      using a2 a1 a8 apply simp
      using a2 a7 a1 a8 apply simp
      using a9 a1 a2 step apply (auto simp add: related_transitions_def Rel_wf_def )[1]
      using a2  apply (fastforce intro:Rel_wf_mon[OF a9])     
                       apply (rule Rel_wf_subset[of _ G\<^sub>c])  
      using a2  apply (fastforce intro:Rel_wf_mon[OF a10])      
      using gc_gc apply auto[1]
                       apply (rule Rel_wf_subset[of _ G\<^sub>s])  
      using a2  apply (fastforce intro:Rel_wf_mon[OF a11])      
      using gs_gs apply auto[1]               
         apply (rule Rel_wf_mon[of  "(length Rels\<^sub>c)-1" "(Rels\<^sub>c ! i)"  "length xs"])
          apply (rule mp[OF spec[OF a13, of i]]) 
      using a00 a2 a1 a8 apply auto[2]
         apply (rule Rel_wf_mon[of  "(length Rels\<^sub>c)-1" "(Rels\<^sub>s ! i)"  "length xs"])
          apply (rule mp[OF spec[OF a12, of i]]) 
      using a00 a2 a1 a8 apply auto[2]
      using a7 apply simp
      using step  a14 by fastforce                                              
  } thus ?thesis by auto qed

lemma p_step_spec_skip:
  assumes
    step:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[(length (xs @ [x]) - 1) := LanguageCon.com.Skip], \<Sigma>g',\<Sigma>ls')" and
    step2:"(\<Gamma>\<^sub>s\<turnstile>\<^sub>p (take (length xs) S, \<Sigma>g', \<Sigma>ls') \<rightarrow>\<^sub>\<tau>\<^sup>* (cs', \<Sigma>g'', \<Sigma>ls'') \<and>
           (\<forall>i<length cs'. cs' ! i = Skip) \<and> cs' \<noteq> [])" and
     a0:"xs \<noteq> []" and
     a1:"length A = length Q \<and> length Q = length S \<and> 
         length Q = length (xs @ [x]) \<and> length (xs @ [x]) \<le> length Rels\<^sub>c"
  shows  "\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>g'', \<Sigma>ls'') \<and>
           (\<forall>i<length c\<^sub>s'. c\<^sub>s' ! i = LanguageCon.com.Skip) \<and> c\<^sub>s' \<noteq> []" 
  proof- 
    have step_last:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[length (xs @ [x]) - 1 := Skip], \<Sigma>g', \<Sigma>ls')"
      using step by auto
    moreover have "S[length (xs @ [x]) - 1 := Skip] = take (length xs) S@[Skip]"
      using a0 a1   
      by (metis (no_types) a1 butlast_conv_take butlast_list_update last_list_update length_0_conv 
           length_butlast list_update_nonempty snoc_eq_iff_butlast)   
    ultimately have a01:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (take (length xs) S@[Skip], \<Sigma>g', \<Sigma>ls')"
      by auto
    moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (take (length xs) S, \<Sigma>g', \<Sigma>ls') \<rightarrow>\<^sub>\<tau>\<^sup>* (cs', \<Sigma>g'', \<Sigma>ls'')" using step2 by auto
    ultimately have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (cs'@[Skip], \<Sigma>g'', \<Sigma>ls'')" 
      using take_refl_tran_clos_step'[of \<Gamma>\<^sub>s S \<Sigma>g \<Sigma>ls "length xs" "[Skip]" \<Sigma>g' \<Sigma>ls' cs']  by auto
    moreover have "\<forall>i<length (cs'@[Skip]). (cs'@[Skip]) ! i = LanguageCon.com.Skip"
      by (metis (mono_tags, lifting) One_nat_def Suc_eq_plus1 l_append length_Cons length_append
               less_antisym list.size(3) nth_append_length step2)    
    moreover have "cs'@[Skip]\<noteq>[]" by auto
    ultimately show ?thesis by auto
  qed

lemma p_step_spec_throw1:
  assumes
    step:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[(length (xs @ [x]) - 1) := Throw], \<Sigma>g',\<Sigma>ls')" and
    step2:"(\<Gamma>\<^sub>s\<turnstile>\<^sub>p (take (length xs) S, \<Sigma>g', \<Sigma>ls') \<rightarrow>\<^sub>\<tau>\<^sup>* (cs', \<Sigma>g'', \<Sigma>ls'') \<and>
           (\<forall>i<length cs'. cs' ! i = Skip \<or> cs' ! i = Throw) \<and> cs' \<noteq> [])" and
     a0:"xs \<noteq> []" and
     a1:"length A = length Q \<and> length Q = length S \<and> 
         length Q = length (xs @ [x]) \<and> length (xs @ [x]) \<le> length Rels\<^sub>c"
  shows  "\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>g'', \<Sigma>ls'') \<and>
           throw_program c\<^sub>s'" 
  proof- 
    have step_last:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[length (xs @ [x]) - 1 := Throw], \<Sigma>g', \<Sigma>ls')"
      using step by auto
    moreover have "S[length (xs @ [x]) - 1 := Throw] = take (length xs) S@[Throw]"
      using a0 a1   
      by (metis (no_types) a1 butlast_conv_take butlast_list_update last_list_update length_0_conv 
           length_butlast list_update_nonempty snoc_eq_iff_butlast)   
    ultimately have a01:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (take (length xs) S@[Throw], \<Sigma>g', \<Sigma>ls')"
      by auto
    moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (take (length xs) S, \<Sigma>g', \<Sigma>ls') \<rightarrow>\<^sub>\<tau>\<^sup>* (cs', \<Sigma>g'', \<Sigma>ls'')" using step2 by auto
    ultimately have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (cs'@[Throw], \<Sigma>g'', \<Sigma>ls'')" 
      using take_refl_tran_clos_step'[of \<Gamma>\<^sub>s S \<Sigma>g \<Sigma>ls "length xs" "[Throw]" \<Sigma>g' \<Sigma>ls' cs']  by auto
    moreover have "\<forall>i<length cs'. cs' ! i = Skip \<or> cs' ! i = Throw"      
      using step2 by auto  
    then have "\<forall>i<length (cs'@[Throw]).  (cs'@[Throw]) ! i = Skip \<or>  (cs'@[Throw]) ! i = Throw"            
      apply auto
      by (metis (no_types) l_append less_antisym nth_append_length)
    moreover have "(\<exists>i<length (cs'@[Throw]). (cs'@[Throw]) ! i = LanguageCon.com.Throw)" by auto
    ultimately show ?thesis unfolding throw_program_def by blast
  qed

lemma p_step_spec_throw:
 assumes
    step:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[(length (xs @ [x]) - 1) := y], \<Sigma>g',\<Sigma>ls')" and
    step2:"(\<Gamma>\<^sub>s\<turnstile>\<^sub>p (take (length xs) S, \<Sigma>g', \<Sigma>ls') \<rightarrow>\<^sub>\<tau>\<^sup>* (cs', \<Sigma>g'', \<Sigma>ls'') \<and>
           throw_program cs')" and
     a0:"xs \<noteq> []" and
     a1:"length A = length Q \<and> length Q = length S \<and> 
         length Q = length (xs @ [x]) \<and> length (xs @ [x]) \<le> length Rels\<^sub>c" and 
     a2:"x = Skip \<and> y = Skip \<or> x = Throw \<and> y = Throw"
  shows  "\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>g'', \<Sigma>ls'') \<and>
           throw_program c\<^sub>s'"
 proof- 
    have step_last:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[length (xs @ [x]) - 1 := y], \<Sigma>g', \<Sigma>ls')"
      using step by auto
    moreover have "S[length (xs @ [x]) - 1 := y] = take (length xs) S@[y]"
      using a0 a1   
      by (metis (no_types) a1 butlast_conv_take butlast_list_update last_list_update length_0_conv 
           length_butlast list_update_nonempty snoc_eq_iff_butlast)   
    ultimately have a01:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (take (length xs) S@[y], \<Sigma>g', \<Sigma>ls')"
      by auto
    moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (take (length xs) S, \<Sigma>g', \<Sigma>ls') \<rightarrow>\<^sub>\<tau>\<^sup>* (cs', \<Sigma>g'', \<Sigma>ls'')" using step2 by auto
    ultimately have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (cs'@[y], \<Sigma>g'', \<Sigma>ls'')" 
      using take_refl_tran_clos_step'[of \<Gamma>\<^sub>s S \<Sigma>g \<Sigma>ls "length xs" "[y]" \<Sigma>g' \<Sigma>ls' cs']  by auto      
    moreover  have "throw_program (cs'@[y])"   
      using step2 a2 unfolding throw_program_def
      apply auto
      apply (metis (no_types) l_append less_antisym nth_append_length)
      apply (metis l_append less_SucI)
      by (metis (no_types) l_append less_antisym nth_append_length)
    ultimately show ?thesis  by blast
  qed


lemma p_step_spec_throw2:
  assumes
    step:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[(length (xs @ [Skip]) - 1) := Skip], \<Sigma>g',\<Sigma>ls')" and
    step2:"(\<Gamma>\<^sub>s\<turnstile>\<^sub>p (take (length xs) S, \<Sigma>g', \<Sigma>ls') \<rightarrow>\<^sub>\<tau>\<^sup>* (cs', \<Sigma>g'', \<Sigma>ls'') \<and>
           throw_program cs')" and
     a0:"xs \<noteq> []" and
     a1:"length A = length Q \<and> length Q = length S \<and> 
         length Q = length (xs @ [x]) \<and> length (xs @ [x]) \<le> length Rels\<^sub>c"
  shows  "\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>g'', \<Sigma>ls'') \<and>
           throw_program c\<^sub>s'" 
  proof- 
    have step_last:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[length (xs @ [x]) - 1 := Skip], \<Sigma>g', \<Sigma>ls')"
      using step by auto
    moreover have "S[length (xs @ [x]) - 1 := Skip] = take (length xs) S@[Skip]"
      using a0 a1   
      by (metis (no_types) a1 butlast_conv_take butlast_list_update last_list_update length_0_conv 
           length_butlast list_update_nonempty snoc_eq_iff_butlast)   
    ultimately have a01:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (take (length xs) S@[Skip], \<Sigma>g', \<Sigma>ls')"
      by auto
    moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (take (length xs) S, \<Sigma>g', \<Sigma>ls') \<rightarrow>\<^sub>\<tau>\<^sup>* (cs', \<Sigma>g'', \<Sigma>ls'')" using step2 by auto
    ultimately have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (cs'@[Skip], \<Sigma>g'', \<Sigma>ls'')" 
      using take_refl_tran_clos_step'[of \<Gamma>\<^sub>s S \<Sigma>g \<Sigma>ls "length xs" "[Skip]" \<Sigma>g' \<Sigma>ls' cs']  by auto      
    moreover  have "throw_program (cs'@[Skip])"   
      using step2 unfolding throw_program_def
      apply auto
      apply (metis (no_types) l_append less_antisym nth_append_length)
      by (metis l_append less_SucI)
    ultimately show ?thesis  by blast
  qed



lemma final_error_1_D:"final_error [x] \<Longrightarrow> (\<exists>f. x = Fault f) \<or> x = Stuck"
  unfolding final_error_def by auto

lemma final_errorD:"final_error (xs@[x]) \<Longrightarrow> x = Skip \<or> x = Throw \<or> x = Stuck \<or> (\<exists>f. x = Fault f)"
  unfolding final_error_def unfolding finalp_def by auto

lemma final_error_singleI:
 "(x = Stuck \<and> y = Stuck) \<or> (x = Fault f \<and> y = Fault f) \<Longrightarrow>   
  final_error_r [x] [y]"
  unfolding final_error_r_def final_error_def finalp_def by auto

lemma final_error_xs: 
  assumes 
  a0:"x = Skip \<or> x = Throw \<or> x = Stuck \<or> x = Fault f" and
  a1:"final_error xs" 
shows "final_error (xs@[x])" 
proof-
  have "(\<forall>i<length xs. finalp (xs ! i)) \<and>
       (\<exists>j<length (xs ). xs ! j = com.Stuck \<or> (\<exists>f. xs ! j = com.Fault f))"
    using a1 unfolding final_error_def by auto
  moreover have "finalp x" unfolding finalp_def using a0 by auto
  ultimately show ?thesis   unfolding final_error_def  apply auto
    by (metis (no_types) l_append less_antisym nth_append_length less_Suc_eq)+
qed

lemma final_error_rD:
  "final_error_r P P' \<Longrightarrow>
   final_error P \<and> final_error P' \<and> 
  (\<forall>i<length P. \<forall>f. P!i = Fault f \<longrightarrow> (\<exists>j<length P'. P'!j = Fault f)) \<and> 
  (\<forall>i<length P. P!i=Stuck \<longrightarrow> (\<exists>j<length P'. P'!j =Stuck)) \<and>
  (\<forall>i<length P'. \<forall>f. P'!i = Fault f \<longrightarrow> (\<exists>j<length P. P!j = Fault f)) \<and> 
  (\<forall>i<length P'. P'!i=Stuck \<longrightarrow> (\<exists>j<length P. P!j =Stuck))"
  unfolding final_error_r_def by auto

lemma final_error_r_xs:
  assumes a0:"(x = Skip \<and> y = Skip) \<or> (x = Throw \<and> y = Throw) \<or>
  (x = Stuck \<and> y = Stuck) \<or> (x = Fault f \<and> y = Fault f)" and  
  a1:"final_error_r xs ys"
shows "final_error_r (xs@[x]) (ys@[y])"
proof-  
  note fe =  final_error_rD[OF a1]
  have "final_error (xs@[x])" using final_error_xs fe a0 by metis
  moreover have "final_error (ys@[y])" using final_error_xs fe a0 by metis
  moreover have "(\<forall>i<length (xs@[x]). \<forall>f. (xs@[x])!i = Fault f \<longrightarrow> 
                   (\<exists>j<length (ys@[y]). (ys@[y])!j = Fault f))" 
    using fe a0 
    by (metis LanguageCon.com.distinct(145) LanguageCon.com.distinct(171) 
               LanguageCon.com.distinct(19) LanguageCon.com.inject(9) 
             l_append length_append_singleton less_Suc_eq nth_append_length) 
  moreover have "(\<forall>i<length (xs@[x]). (xs@[x])!i =Stuck \<longrightarrow> 
                   (\<exists>j<length (ys@[y]). (ys@[y])!j = Stuck))"
     using fe a0
     by (metis LanguageCon.com.distinct(13) LanguageCon.com.distinct(145) LanguageCon.com.distinct(147) 
               l_append length_append_singleton less_Suc_eq nth_append_length)                    
  moreover have "(\<forall>i<length (ys@[y]). \<forall>f. (ys@[y])!i = Fault f \<longrightarrow> 
                   (\<exists>j<length (xs@[x]). (xs@[x])!j = Fault f))"
   using fe a0
    by (metis LanguageCon.com.distinct(145) LanguageCon.com.distinct(19) LanguageCon.com.inject(9) 
                 LanguageCon.com.simps(183)  
                  l_append length_append_singleton less_Suc_eq nth_append_length) 
  moreover have "(\<forall>i<length (ys@[y]). (ys@[y])!i = Stuck \<longrightarrow> 
                   (\<exists>j<length (xs@[x]). (xs@[x])!j = Stuck))" using a0 fe
    by (metis LanguageCon.com.distinct(145) LanguageCon.com.simps(159) LanguageCon.com.simps(25) 
          l_append length_append_singleton less_Suc_eq nth_append_length)    
  ultimately show ?thesis unfolding final_error_r_def by auto
qed


lemma final_error_skip_throw: 
  assumes 
  a0:" \<not> final_error xs" and
  a1:"final_error (xs @ [x])"
shows "\<forall>i<length xs. xs ! i = Skip \<or> xs ! i = Throw"
proof-
  have "\<forall>i<length (xs@[x]). finalp  ((xs@[x]) ! i)"
    using a1 unfolding final_error_def by auto
  moreover have "\<forall>j<length xs. \<not>(xs!j = Stuck) \<and> \<not>(\<exists>f. xs!j = Fault f)"
    using calculation a0 unfolding final_error_def
    by (metis l_append length_append_singleton less_Suc_eq)  
  ultimately show ?thesis unfolding finalp_def
    using l_append less_Suc_eq by fastforce
qed                             


lemma final_error_stuck_fault: 
  assumes 
  a0:" \<not> final_error xs" and
  a1:"final_error (xs @ [x])"
shows "x = Stuck \<or> (\<exists>f. x = Fault f)"
proof-
  have "\<forall>i<length xs. xs ! i = Skip \<or> xs ! i = Throw" 
    using final_error_skip_throw[OF a0 a1] by auto  
  then show ?thesis 
    using a1 unfolding final_error_def
    using l_append less_Suc_eq by fastforce
qed                             

lemma final_error_r_last: assumes
  a0:"\<forall>i<length xs. xs!i = Skip \<or> xs!i = Throw" and 
  a1:"\<forall>i<length ys. ys!i = Skip \<or> ys!i = Throw" and
  a2:"length (ys@[y]) = length (xs@[x])" and
  a3:"x = Stuck \<and> y  = Stuck \<or> (\<exists>f. x = Fault f \<and> y = Fault f)"
shows "final_error_r (xs@[x]) (ys@[y])" 
proof-
  have "final_error (xs@[x])" unfolding final_error_def finalp_def using a0 a3
    using l_append less_Suc_eq by fastforce
  moreover have "final_error  (ys@[y])" 
    unfolding final_error_def finalp_def using a1 a3
    using l_append less_Suc_eq by fastforce
  moreover have 
    "(\<forall>i<length (xs @ [x]). \<forall>f. (xs @ [x]) ! i = com.Fault f \<longrightarrow> 
        (\<exists>j<length (ys @ [y]). (ys @ [y]) ! j = com.Fault f))"
    using a0 a3
    by (metis LanguageCon.com.distinct(145) LanguageCon.com.distinct(171) 
            LanguageCon.com.distinct(19) LanguageCon.com.inject(9) a2 butlast_snoc 
            l_append length_append_singleton length_butlast less_antisym nth_append_length )     
  moreover have "(\<forall>i<length (xs @ [x]). (xs @ [x]) ! i = com.Stuck \<longrightarrow> 
                   (\<exists>j<length (ys @ [y]). (ys @ [y]) ! j = com.Stuck))"
    using a0 a3
    by (metis LanguageCon.com.distinct(13) LanguageCon.com.distinct(145) 
          LanguageCon.com.distinct(147) a2 cancel_comm_monoid_add_class.diff_cancel diff_Suc_1 
         length_append_singleton  less_antisym nth_Cons_0 nth_append )    
  moreover have "(\<forall>i<length (ys @ [y]). \<forall>f. (ys @ [y]) ! i = com.Fault f \<longrightarrow> 
                  (\<exists>j<length (xs @ [x]). (xs @ [x]) ! j = com.Fault f))"
    using a1 a2 a3  length_append_singleton less_Suc_eq
    by (metis LanguageCon.com.distinct(145) LanguageCon.com.distinct(19) LanguageCon.com.inject(9) 
              LanguageCon.com.simps(183) Suc_leI append1_eq_conv drop_all id_take_nth_drop l_append)
    
  moreover have "(\<forall>i<length (ys @ [y]). (ys @ [y]) ! i = com.Stuck \<longrightarrow> 
                   (\<exists>j<length (xs @ [x]). (xs @ [x]) ! j = com.Stuck))"
    using a1 a2 a3
    by (metis LanguageCon.com.distinct(13) LanguageCon.com.distinct(145) LanguageCon.com.distinct(147) 
          l_append length_append_singleton less_antisym nat.inject nth_append_length)
  ultimately show ?thesis unfolding final_error_r_def by auto
qed

lemma p_step_spec_error:
 assumes
    step:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[(length (xs @ [x]) - 1) := y], \<Sigma>g',\<Sigma>ls')" and
    step2:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (take (length xs) S, \<Sigma>g', \<Sigma>ls') \<rightarrow>\<^sub>\<tau>\<^sup>* (cs', \<Sigma>g'', \<Sigma>ls'')" and
    a0:"xs \<noteq> []" and a0':"final_error_r xs cs'" and
    a1:"length A = length Q \<and> length Q = length S \<and> 
         length Q = length (xs @ [x]) \<and> length (xs @ [x]) \<le> length Rels\<^sub>c" and
  a2:"x = Skip \<and> y = Skip \<or> x = Throw \<and> y = Throw \<or> 
       x = Stuck \<and> y  = Stuck \<or> (\<exists>f. x = Fault f \<and> y = Fault f)"
  shows  "\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>g'', \<Sigma>ls'') \<and> final_error_r (xs@[x]) c\<^sub>s'" 
proof-
    have step_last:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[length (xs @ [x]) - 1 := y], \<Sigma>g', \<Sigma>ls')"
      using step by auto
    moreover have "S[length (xs @ [x]) - 1 := y] = take (length xs) S@[y]"
      using a0 a1   
      by (metis (no_types) a1 butlast_conv_take butlast_list_update last_list_update length_0_conv 
           length_butlast list_update_nonempty snoc_eq_iff_butlast)   
    ultimately have a01:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (take (length xs) S@[y], \<Sigma>g', \<Sigma>ls')"
      by auto
    moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (take (length xs) S, \<Sigma>g', \<Sigma>ls') \<rightarrow>\<^sub>\<tau>\<^sup>* (cs', \<Sigma>g'', \<Sigma>ls'')" using step2 by auto
    ultimately have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (cs'@[y], \<Sigma>g'', \<Sigma>ls'')" 
      using take_refl_tran_clos_step'[of \<Gamma>\<^sub>s S \<Sigma>g \<Sigma>ls "length xs" "[y]" \<Sigma>g' \<Sigma>ls' cs']  by auto      
    moreover  have "final_error_r (xs@[x]) (cs'@[y])"
      using a0' a2  by (auto intro: final_error_r_xs)
    ultimately show ?thesis  by blast
  qed

lemma p_step_spec_error1:
 assumes
    step:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[(length (xs @ [x]) - 1) := y], \<Sigma>g',\<Sigma>ls')" and
    step2:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (take (length xs) S, \<Sigma>g', \<Sigma>ls') \<rightarrow>\<^sub>\<tau>\<^sup>* (cs', \<Sigma>g'', \<Sigma>ls'')" and
    a0:"xs \<noteq> []" and a0':"\<forall>i<length cs'. cs'!i = Skip \<or> cs'!i = Throw" and 
    a0'':"\<forall>i<length xs. xs!i = Skip \<or> xs!i = Throw" and
    a1:"length A = length Q \<and> length Q = length S \<and> 
         length Q = length (xs @ [x]) \<and> length (xs @ [x]) \<le> length Rels\<^sub>c" and
  a2:"x = Stuck \<and> y  = Stuck \<or> (\<exists>f. x = Fault f \<and> y = Fault f)"
  shows  "\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>g'', \<Sigma>ls'') \<and> final_error_r (xs@[x]) c\<^sub>s'" 
proof-
    have step_last:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[length (xs @ [x]) - 1 := y], \<Sigma>g', \<Sigma>ls')"
      using step by auto
    moreover have "S[length (xs @ [x]) - 1 := y] = take (length xs) S@[y]"
      using a0 a1   
      by (metis (no_types) a1 butlast_conv_take butlast_list_update last_list_update length_0_conv 
           length_butlast list_update_nonempty snoc_eq_iff_butlast)   
    ultimately have a01:"\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (take (length xs) S@[y], \<Sigma>g', \<Sigma>ls')"
      by auto
    moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (take (length xs) S, \<Sigma>g', \<Sigma>ls') \<rightarrow>\<^sub>\<tau>\<^sup>* (cs', \<Sigma>g'', \<Sigma>ls'')" using step2 by auto
    ultimately have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (cs'@[y], \<Sigma>g'', \<Sigma>ls'')" 
      using take_refl_tran_clos_step'[of \<Gamma>\<^sub>s S \<Sigma>g \<Sigma>ls "length xs" "[y]" \<Sigma>g' \<Sigma>ls' cs']  by auto      
    moreover have "length (cs'@[y]) = length S"
      by (metis (no_types) calculation tran_step_par_same_len_program)
    then  have "final_error_r (xs@[x]) (cs'@[y])" 
      using  final_error_r_last[OF a0'' a0' _ a2] a1
      by auto
    ultimately show ?thesis  by blast
  qed

lemma  tran_in_Guar:
  assumes 
    step:"(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)\<and> 
         (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> 
             ((Guas\<^sub>c ! (length (xs @ [x]) - 1)), ((Guas\<^sub>s ! (length (xs @ [x]) - 1)))\<^sup>*)\<^sub>\<alpha> " and
    step2:"(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g', \<Sigma>ls'), \<Sigma>g'', \<Sigma>ls'') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
          (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g', \<Sigma>ls'), \<Sigma>g'', \<Sigma>ls'') \<in> 
               (\<Union> ((!) Guas\<^sub>c ` {..<length (take (length xs) Q)}), 
                (\<Union> ((!) Guas\<^sub>s ` {..<length (take (length xs) Q)}))\<^sup>*)\<^sub>\<alpha>" and
    a0:"xs \<noteq> []" and
    a1:"0 < length Q" and
    a2:"length A = length Q \<and> length Q = length S \<and> length Q = length (xs @ [x]) \<and> 
        length (xs @ [x]) \<le> length Rels\<^sub>c"
  shows "(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> 
          (\<Union> ((!) Guas\<^sub>c ` {..<length Q}), (\<Union> ((!) Guas\<^sub>s ` {..<length Q}))\<^sup>*)\<^sub>\<alpha>" 
proof-       
  let ?Q = "take (length xs) Q"
  have "(Guas\<^sub>s ! (length (xs @ [x]) - 1))\<^sup>* \<subseteq>(\<Union> ((!) Guas\<^sub>s ` {..<length Q}))\<^sup>* "
    using a0 a1 a2 apply auto
    by (metis (no_types) G_comp_aux' UN_upper lessI lessThan_iff)
  moreover have "(\<Union> ((!) Guas\<^sub>s ` {..<length ?Q}))\<^sup>* \<subseteq> (\<Union> ((!) Guas\<^sub>s ` {..<length Q}))\<^sup>*"
  proof- 
    have "\<Union> ((!) Guas\<^sub>s ` {..<length ?Q}) \<subseteq> \<Union> ((!) Guas\<^sub>s ` {..<length Q})"
      using a0 a1 a2 by auto
    thus ?thesis 
      by (simp add: rtrancl_mono) 
  qed    
  ultimately show ?thesis using step step2 
    unfolding related_transitions_def by (auto intro: tran_G)
qed 

lemma tran_in_Q:
  assumes               
    a2:"0 < length Q" and
    a3:" length Q = length (xs @ [x]) \<and> length (xs @ [x]) \<le> length Rels\<^sub>c" and
    a4:"length Rels\<^sub>c = length Guas\<^sub>c \<and>
          length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s " and
    a5:"\<forall>i<length Rels\<^sub>c.
       R\<^sub>c \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. (Guas\<^sub>c ! j)) \<subseteq> (Rels\<^sub>c ! i) \<and>
       R\<^sub>s \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. (Guas\<^sub>s ! j)) \<subseteq> (Rels\<^sub>s!i)" and
    a6:"\<forall>i<length Q. Sta\<^sub>s (Q ! i) (Rels\<^sub>c ! i, (Rels\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha>" and
    step:"((\<sigma>g, \<sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> Q ! (length (xs @ [x]) - 1) " and
    step2:"(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g', \<Sigma>ls'), \<Sigma>g'', \<Sigma>ls'') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
          (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g', \<Sigma>ls'), \<Sigma>g'', \<Sigma>ls'') \<in> 
               (\<Union> ((!) Guas\<^sub>c ` {..<length  (take (length xs) Q)}), (\<Union> ((!) Guas\<^sub>s ` {..<length (take (length xs) Q)}))\<^sup>*)\<^sub>\<alpha> \<and>
           ((\<sigma>g, \<sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> \<Inter> ((!)  (take (length xs) Q) ` {..<length  (take (length xs) Q)})" 
  shows "((\<sigma>g, \<sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> \<Inter> ((!) Q ` {..<length Q})"
proof-  
  have len: "length (take (length xs) Q) = length xs"
    using  a3 by auto      
  have subset:"\<Union> ((!) Guas\<^sub>s ` {..<length (take (length xs) Q)}) \<subseteq>
        \<Union> ((!) Guas\<^sub>s ` {i. i \<noteq> length xs \<and> i < length Guas\<^sub>s})"
    using a3 a4 dual_order.strict_trans nat_neq_iff by auto    
  then have set_eq: "(\<Union> ((!) Guas\<^sub>c ` {..<length  (take (length xs) Q)}), 
                        (\<Union> ((!) Guas\<^sub>s ` {..<length (take (length xs) Q)}))\<^sup>*)\<^sub>\<alpha> \<subseteq>
                      (\<Union> ((!) Guas\<^sub>c ` {i. i \<noteq> length xs \<and> i < length Guas\<^sub>s}), 
                        (\<Union> ((!) Guas\<^sub>s ` {i. i \<noteq> length xs \<and> i < length Guas\<^sub>s}))\<^sup>*)\<^sub>\<alpha>"
    unfolding related_transitions_def apply auto
    using a3 a4 nat_neq_iff  
    by (auto simp add: G_comp_aux1)    
  have rel:"(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g', \<Sigma>ls'), \<Sigma>g'', \<Sigma>ls'') \<in> 
          (Rels\<^sub>c ! (length (xs @ [x]) - 1), (Rels\<^sub>s ! (length (xs @ [x]) - 1))\<^sup>*)\<^sub>\<alpha>" 
    apply (rule guar_i_rely_j'[OF a4])
    using a4 a5 apply auto[2] 
    using step2 len set_eq a4  apply (auto simp add:  a4)[1]
    using  a3  by auto     
  moreover have "((\<sigma>g, \<sigma>ls), \<Sigma>g', \<Sigma>ls') \<in> Q ! (length (xs @ [x]) - 1)"
    using step by auto    
  ultimately have "((\<sigma>g, \<sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> Q ! (length (xs @ [x]) - 1)"
     using a3 a2 unfolding Sta\<^sub>s_def related_transitions_def
     by (metis (no_types, lifting) rel  a6 diff_less sim_env zero_less_one)     
  then show ?thesis using  a3  step2 apply auto 
    by (metis (no_types) len length_take lessThan_iff nat_neq_iff not_less_eq)
qed

lemma tran_in_A:
  assumes               
    a2:"0 < length Q" and
    a3:" length Q = length (xs @ [x]) \<and> length (xs @ [x]) \<le> length Rels\<^sub>c" and
    a4:"length Rels\<^sub>c = length Guas\<^sub>c \<and>
          length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s " and
    a5:"\<forall>i<length Rels\<^sub>c.
       R\<^sub>c \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. (Guas\<^sub>c ! j)) \<subseteq> (Rels\<^sub>c ! i) \<and>
       R\<^sub>s \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. (Guas\<^sub>s ! j)) \<subseteq> (Rels\<^sub>s!i)" and
    a6:"\<forall>i<length Q. Sta\<^sub>s (Q ! i) (Rels\<^sub>c ! i, (Rels\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha>" and
    step:"((\<sigma>g, \<sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> Q ! (length (xs @ [x]) - 1) " and
    step2:"(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g', \<Sigma>ls'), \<Sigma>g'', \<Sigma>ls'') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
          (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g', \<Sigma>ls'), \<Sigma>g'', \<Sigma>ls'') \<in> 
               (\<Union> ((!) Guas\<^sub>c ` {..<length  (take (length xs) Q)}), 
               (\<Union> ((!) Guas\<^sub>s ` {..<length (take (length xs) Q)}))\<^sup>*)\<^sub>\<alpha>" 
  shows "((\<sigma>g, \<sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> \<Union> ((!) Q ` {..<length Q})"
proof-  
  have len: "length (take (length xs) Q) = length xs"
    using  a3 by auto      
  have subset:"\<Union> ((!) Guas\<^sub>s ` {..<length (take (length xs) Q)}) \<subseteq>
        \<Union> ((!) Guas\<^sub>s ` {i. i \<noteq> length xs \<and> i < length Guas\<^sub>s})"
    using a3 a4 dual_order.strict_trans nat_neq_iff by auto    
  then have set_eq: "(\<Union> ((!) Guas\<^sub>c ` {..<length  (take (length xs) Q)}), 
                        (\<Union> ((!) Guas\<^sub>s ` {..<length (take (length xs) Q)}))\<^sup>*)\<^sub>\<alpha> \<subseteq>
                      (\<Union> ((!) Guas\<^sub>c ` {i. i \<noteq> length xs \<and> i < length Guas\<^sub>s}), 
                        (\<Union> ((!) Guas\<^sub>s ` {i. i \<noteq> length xs \<and> i < length Guas\<^sub>s}))\<^sup>*)\<^sub>\<alpha>"
    unfolding related_transitions_def apply auto
    using a3 a4 nat_neq_iff  
    by (auto simp add: G_comp_aux1)    
  have rel:"(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g', \<Sigma>ls'), \<Sigma>g'', \<Sigma>ls'') \<in> 
          (Rels\<^sub>c ! (length (xs @ [x]) - 1), (Rels\<^sub>s ! (length (xs @ [x]) - 1))\<^sup>*)\<^sub>\<alpha>" 
    apply (rule guar_i_rely_j'[OF a4])
    using a4 a5 apply auto[2] 
    using step2 len set_eq a4  apply (auto simp add:  a4)[1]
    using  a3  by auto     
  moreover have "((\<sigma>g, \<sigma>ls), \<Sigma>g', \<Sigma>ls') \<in> Q ! (length (xs @ [x]) - 1)"
    using step by auto    
  ultimately have "((\<sigma>g, \<sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> Q ! (length (xs @ [x]) - 1)"
     using a3 a2 unfolding Sta\<^sub>s_def related_transitions_def
     by (metis (no_types, lifting) rel  a6 diff_less sim_env zero_less_one)     
  then show ?thesis using  a3  step2 by auto 
qed


lemma sim_final_skip: assumes 
  a0':"length Rels\<^sub>c = length Guas\<^sub>c \<and>
         length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s " and
  a01:"length PostsA = length PostsQ \<and> length PostsQ = length S \<and> 
       length PostsQ = length C \<and> length C \<le> length Rels\<^sub>c" and
  a0''':"length PostsQ >0" and
  a0:"\<forall>i<length Rels\<^sub>c.
       R\<^sub>c \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. (Guas\<^sub>c ! j)) \<subseteq> (Rels\<^sub>c ! i) \<and>
       R\<^sub>s \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. (Guas\<^sub>s ! j)) \<subseteq> (Rels\<^sub>s!i)" and
  a1:" (\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)) \<subseteq> G\<^sub>c" and
  a2:" (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s ! j)) \<subseteq> G\<^sub>s" and               
  a6:"Rel_wf  ((length Rels\<^sub>c)-1) \<alpha>" and a6':"Rel_wf ((length Rels\<^sub>c)-1) G\<^sub>c" and a6'':"Rel_wf ((length Rels\<^sub>c)-1) G\<^sub>s" and
  a7:"\<forall>i<length Rels\<^sub>c. Rel_wf ((length Rels\<^sub>c)-1) (Rels\<^sub>s ! i)" and
  a8:"\<forall>i<length Rels\<^sub>c. Rel_wf ((length Rels\<^sub>c)-1) (Rels\<^sub>c ! i)" and
  a9:"(\<forall>i<length C. C ! i = LanguageCon.com.Skip)" and
  a10:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a11:"\<gamma>\<^sub>a \<subseteq> \<alpha>" and 
  a12: "C \<noteq> []" and 
  a13:"\<forall>i<length C. 
        (\<Gamma>\<^sub>c, (C ! i,toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c !i), Seq_rel i (Guas\<^sub>c!i)) 
                 \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>) 
        (\<Gamma>\<^sub>s,(S! i,toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s!i), Seq_rel i (Guas\<^sub>s !i))" and
  a15:"((\<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls)) \<in> \<alpha>" and a16:"length \<sigma>ls  = length \<Sigma>ls" and a17:"length Rels\<^sub>c = length \<sigma>ls" and 
  a20:"\<forall>i<length PostsQ. Rel_wf i (PostsQ ! i)" and
  a21:"\<forall>i<length PostsQ. Sta\<^sub>s (PostsQ!i) ((Rels\<^sub>c!i), ((Rels\<^sub>s!i)\<^sup>*))\<^sub>\<alpha>" 
shows "\<exists>ab bb. (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
               (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> 
                   ((\<Union>j<length PostsQ. (Guas\<^sub>c !j)), (\<Union>j<length PostsQ. (Guas\<^sub>s ! j))\<^sup>*)\<^sub>\<alpha> \<and>
                 ((\<sigma>g, \<sigma>ls), ab, bb) \<in> (\<Inter>i<length PostsQ.  (PostsQ ! i)) \<and> \<gamma>\<^sub>n \<subseteq> \<alpha> \<and>
              (\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', ab, bb) \<and>
                    (\<forall>i<length c\<^sub>s'. c\<^sub>s' ! i = LanguageCon.com.Skip) \<and> c\<^sub>s' \<noteq> [])"
  using a12 a9 a13  a15 a16  a20 a0''' a01 a21
proof(induction arbitrary:  S  \<Sigma>g \<Sigma>ls PostsQ PostsA  rule:rev_nonempty_induct)
  case (single x S  \<Sigma>g \<Sigma>ls Q A)
  then show ?case using 
      sim_final_1[OF a0' single(1,2,3,4,5,6,7) a6 a6' a6'' a1 a2 a17 a10] by auto
next
  case (snoc x xs  S \<Sigma>g \<Sigma>ls Q A)
  let ?i = "length (xs@[x]) - 1"
  let ?Q = "take (length xs) Q"
  let ?A = "take (length xs) A" 
  let ?S = "take (length xs) S"
   have h1:"\<forall>i<length xs. xs!i = Skip" using snoc(3) 
    by (metis Suc_lessD Suc_mono l_append length_Cons length_rotate1 rotate1.simps(2))
  have h3:"\<forall>i<length ?Q. Sim_Rules.Rel_wf i (?Q ! i)" 
    using snoc(7) by auto
  have h4:"0 < length ?Q" using snoc by auto
  have h5:"length ?A = length ?Q \<and>
     length ?Q = length ?S \<and> length ?Q = length xs \<and> length xs \<le> length Rels\<^sub>c"
    using snoc(9) by auto
  have h6:" \<forall>i<length ?Q. Sta\<^sub>s (?Q ! i) 
                            ((Rels\<^sub>c ! i),((Rels\<^sub>s ! i)\<^sup>*))\<^sub>\<alpha>"
    using snoc(10) by auto
  have sim:"(\<Gamma>\<^sub>c,(Skip, toSeqState ?i (\<sigma>g, \<sigma>ls)),Seq_rel ?i (Rels\<^sub>c ! ?i),Seq_rel ?i (Guas\<^sub>c ! ?i))
     \<succeq>\<^sub>(\<^sub>Seq_rel ?i \<alpha>\<^sub>;\<^sub>xx ?i Q\<^sub>;\<^sub>xx ?i A\<^sub>)
     (\<Gamma>\<^sub>s,(S ! ?i, toSeqState ?i (\<Sigma>g, \<Sigma>ls)),Seq_rel ?i (Rels\<^sub>s ! ?i),Seq_rel ?i (Guas\<^sub>s ! ?i))" 
    using snoc(4,3,8,9) by auto       
  have "\<exists>\<Sigma>g' \<Sigma>ls'.
         (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> ((Guas\<^sub>c ! ?i), ((Guas\<^sub>s ! ?i))\<^sup>*)\<^sub>\<alpha> \<and>
         ((\<sigma>g, \<sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> Q ! ?i \<and>
         \<gamma>\<^sub>n \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[?i := LanguageCon.com.Skip], \<Sigma>g',\<Sigma>ls')"             
    apply (rule sim_final_i[OF sim[simplified xx_def]])
    using snoc apply auto[3] 
    using a6 a6' a6'' snoc(9) a17 a10 a0' a2 a1  Rel_wf_mon[of "((length Rels\<^sub>c)-1)"] by force+
  then obtain \<Sigma>g' \<Sigma>ls' where step:"
         (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)\<and> 
         (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> ((Guas\<^sub>c ! ?i), ((Guas\<^sub>s ! ?i))\<^sup>*)\<^sub>\<alpha> \<and>
         ((\<sigma>g, \<sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> Q ! ?i \<and>
         \<gamma>\<^sub>n \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[?i := LanguageCon.com.Skip], \<Sigma>g',\<Sigma>ls')"
    by auto   
  have "?i < length \<Sigma>ls'"
  proof-
    show ?thesis using a6 a0' snoc(9) step unfolding related_transitions_def Rel_wf_def by auto
  qed 
  have sim_i:"\<forall>i<length xs.
       (\<Gamma>\<^sub>c,(xs ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
         \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i Q\<^sub>;\<^sub>xx i A\<^sub>)
       (\<Gamma>\<^sub>s,(S ! i, toSeqState i (\<Sigma>g', \<Sigma>ls')),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))"
    using sim_i[OF _ snoc(4) a0' snoc(9) a0 a1 a2 snoc(1) snoc(6) a17 a6 a6' a6'' a7 a8] 
         step eq_length_pev_tran_step'
    by fast
  have 
  h2:"\<forall>i<length xs. (\<Gamma>\<^sub>c,(xs ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
        \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i ?Q\<^sub>;\<^sub>xx i ?A\<^sub>)
        (\<Gamma>\<^sub>s,(?S ! i, toSeqState i (\<Sigma>g', \<Sigma>ls')),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))"  
  proof-
  {
    fix i
    assume a00:"i<length xs"
    then have "xs!i = (xs@[x])!i" and a00':"i<length (xs)"
      by (auto simp add: l_append)
    moreover have "?Q!i = Q!i" using a00 by auto
    moreover have "?A!i = A!i" using a00 by auto
    moreover have "?S!i = S!i" using a00 by auto        
    ultimately have "(\<Gamma>\<^sub>c,(xs ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
        \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i ?Q\<^sub>;\<^sub>xx i ?A\<^sub>)
        (\<Gamma>\<^sub>s,(?S ! i, toSeqState i (\<Sigma>g', \<Sigma>ls')),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))"
      using sim_i unfolding xx_def by fastforce 
  } thus ?thesis by auto qed    
  have hm:"length \<sigma>ls = length \<Sigma>ls'" using step eq_length_pev_tran_step' snoc(6) by auto
  obtain \<Sigma>g'' \<Sigma>ls'' cs' where 
        step2:"(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g', \<Sigma>ls'), \<Sigma>g'', \<Sigma>ls'') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
          (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g', \<Sigma>ls'), \<Sigma>g'', \<Sigma>ls'') \<in> 
               (\<Union> ((!) Guas\<^sub>c ` {..<length ?Q}), (\<Union> ((!) Guas\<^sub>s ` {..<length ?Q}))\<^sup>*)\<^sub>\<alpha> \<and>
           ((\<sigma>g, \<sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> \<Inter> ((!) ?Q ` {..<length ?Q})  \<and>
           \<gamma>\<^sub>n \<subseteq> \<alpha> \<and>
           (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (?S, \<Sigma>g', \<Sigma>ls') \<rightarrow>\<^sub>\<tau>\<^sup>* (cs', \<Sigma>g'', \<Sigma>ls'') \<and>
            (\<forall>i<length cs'. cs' ! i = Skip) \<and> cs' \<noteq> [])"
    using snoc(2)[OF h1 h2 _ hm h3 h4 h5 h6] step unfolding related_transitions_def  by auto
  then have "\<exists>c\<^sub>s'.
               \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>g'', \<Sigma>ls'') \<and>
               (\<forall>i<length c\<^sub>s'. c\<^sub>s' ! i = LanguageCon.com.Skip) \<and> c\<^sub>s' \<noteq> []" 
    using p_step_spec_skip[OF _ _  snoc(1,9)] step step2 by auto
  moreover have "(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> 
             (\<Union> ((!) Guas\<^sub>c ` {..<length Q}), (\<Union> ((!) Guas\<^sub>s ` {..<length Q}))\<^sup>*)\<^sub>\<alpha>"
    using tran_in_Guar[OF _ _ snoc(1,8,9)] step step2 by fast  
  moreover have "((\<sigma>g, \<sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> \<Inter> ((!) Q ` {..<length Q})"     
    apply (rule tran_in_Q[OF snoc(8) _ a0' a0 snoc(10)])
    using step step2 snoc(9) by auto    
  moreover have "(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
    using step step2 unfolding related_transitions_def by auto
  ultimately have 
        "(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
         (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> 
             (\<Union> ((!) Guas\<^sub>c ` {..<length Q}), (\<Union> ((!) Guas\<^sub>s ` {..<length Q}))\<^sup>*)\<^sub>\<alpha> \<and>
           ((\<sigma>g, \<sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> \<Inter> ((!) Q ` {..<length Q})  \<and>
           \<gamma>\<^sub>n \<subseteq> \<alpha> \<and>
           (\<exists>c\<^sub>s'.
               \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>g'', \<Sigma>ls'') \<and>
               (\<forall>i<length c\<^sub>s'. c\<^sub>s' ! i = LanguageCon.com.Skip) \<and> c\<^sub>s' \<noteq> [])"
    using step step2 by auto    
  then show ?case by auto
qed


lemma sim_final_throw: assumes 
  a0':"length Rels\<^sub>c = length Guas\<^sub>c \<and>
         length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s " and
  a01:"length PostsA = length PostsQ \<and> length PostsQ = length S \<and> 
       length PostsQ = length C \<and> length C \<le> length Rels\<^sub>c" and
  a0''':"length PostsQ >0" and
  a0:"\<forall>i<length Rels\<^sub>c.
       R\<^sub>c \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. (Guas\<^sub>c ! j)) \<subseteq> (Rels\<^sub>c ! i) \<and>
       R\<^sub>s \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. (Guas\<^sub>s ! j)) \<subseteq> (Rels\<^sub>s!i)" and
  a1:" (\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)) \<subseteq> G\<^sub>c" and
  a2:" (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s ! j)) \<subseteq> G\<^sub>s" and               
  a6:"Rel_wf  ((length Rels\<^sub>c)-1) \<alpha>" and a6':"Rel_wf ((length Rels\<^sub>c)-1) G\<^sub>c" and a6'':"Rel_wf ((length Rels\<^sub>c)-1) G\<^sub>s" and
  a7:"\<forall>i<length Rels\<^sub>c. Rel_wf ((length Rels\<^sub>c)-1) (Rels\<^sub>s ! i)" and
  a8:"\<forall>i<length Rels\<^sub>c. Rel_wf ((length Rels\<^sub>c)-1) (Rels\<^sub>c ! i)" and
  a9:"throw_program C" and a9':"C\<noteq>[]" and
  a10:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a11:"\<gamma>\<^sub>a \<subseteq> \<alpha>" and 
  a13:"\<forall>i<length C. 
        (\<Gamma>\<^sub>c, (C ! i,toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c !i), Seq_rel i (Guas\<^sub>c!i)) 
                 \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>) 
        (\<Gamma>\<^sub>s,(S! i,toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s!i), Seq_rel i (Guas\<^sub>s !i))" and
  a15:"((\<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls)) \<in> \<alpha>" and a16:"length \<sigma>ls  = length \<Sigma>ls" and a17:"length Rels\<^sub>c = length \<sigma>ls" and 
  a20:"\<forall>i<length PostsQ. Rel_wf i (PostsA ! i)" and  a20':"\<forall>i<length PostsQ. Rel_wf i (PostsQ ! i)" and
  a21:"\<forall>i<length PostsQ. Sta\<^sub>s (PostsQ!i) ((Rels\<^sub>c!i), ((Rels\<^sub>s!i)\<^sup>*))\<^sub>\<alpha>" and
  a22:"\<forall>i<length PostsQ. Sta\<^sub>s (PostsA!i) ((Rels\<^sub>c!i), ((Rels\<^sub>s!i)\<^sup>*))\<^sub>\<alpha>" 
shows "\<exists>ab bb. (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
               (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> 
                   ((\<Union>j<length PostsQ. (Guas\<^sub>c !j)), (\<Union>j<length PostsQ. (Guas\<^sub>s ! j))\<^sup>*)\<^sub>\<alpha> \<and>
                 ((\<sigma>g, \<sigma>ls), ab, bb) \<in> (\<Union>i<length PostsA.  (PostsA ! i)) \<and> \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
              (\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', ab, bb) \<and> throw_program c\<^sub>s')"
  using  a9' a9 a13  a15 a16  a20 a0''' a01 a21 a20' a22
proof(induction arbitrary:  S  \<Sigma>g \<Sigma>ls PostsQ PostsA  rule:rev_nonempty_induct)
  case (single x S  \<Sigma>g \<Sigma>ls Q A)  
  show ?case using single(1)
      sim_final_throw_1[OF a0' _ single(2,3,4,5,6,7) a6 a6' a6'' a1 a2 a17 a11] 
    unfolding throw_program_def by auto
next
  case (snoc x xs  S \<Sigma>g \<Sigma>ls Q A)
  let ?i = "length (xs@[x]) - 1"
  let ?Q = "take (length xs) Q"
  let ?A = "take (length xs) A" 
  let ?S = "take (length xs) S"
  have h0:"x = Skip \<or> x = Throw"
    using snoc(3) unfolding throw_program_def by auto  
  have h3:"\<forall>i<length ?Q. Sim_Rules.Rel_wf i (?A ! i)" 
    using snoc(7) by auto
  have h3':"\<forall>i<length ?Q. Sim_Rules.Rel_wf i (?Q ! i)"
    using snoc(11) snoc(9) by auto
  have h4:"0 < length ?Q" using snoc by auto
  have h5:"length ?A = length ?Q \<and>
     length ?Q = length ?S \<and> length ?Q = length xs \<and> length xs \<le> length Rels\<^sub>c"
    using snoc(9) by auto
  have h6:" \<forall>i<length ?Q. Sta\<^sub>s (?Q ! i) 
                            ((Rels\<^sub>c ! i),((Rels\<^sub>s ! i)\<^sup>*))\<^sub>\<alpha>"
    using snoc(10) by auto  
  have h7:" \<forall>i<length ?Q. Sta\<^sub>s (?A ! i) 
                            ((Rels\<^sub>c ! i),((Rels\<^sub>s ! i)\<^sup>*))\<^sub>\<alpha>"
    using snoc(12) by auto
  have sim:"(\<Gamma>\<^sub>c,(x, toSeqState ?i (\<sigma>g, \<sigma>ls)),Seq_rel ?i (Rels\<^sub>c ! ?i),Seq_rel ?i (Guas\<^sub>c ! ?i))
     \<succeq>\<^sub>(\<^sub>Seq_rel ?i \<alpha>\<^sub>;\<^sub>xx ?i Q\<^sub>;\<^sub>xx ?i A\<^sub>)
     (\<Gamma>\<^sub>s,(S ! ?i, toSeqState ?i (\<Sigma>g, \<Sigma>ls)),Seq_rel ?i (Rels\<^sub>s ! ?i),Seq_rel ?i (Guas\<^sub>s ! ?i))" 
      using x snoc(4,3,8,9) by auto  
  have "\<exists>\<Sigma>g' \<Sigma>ls' y. 
       (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
        (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> ((Guas\<^sub>c ! ?i), ((Guas\<^sub>s ! ?i))\<^sup>*)\<^sub>\<alpha> \<and> 
        (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S , \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[?i:=y], \<Sigma>g',\<Sigma>ls') \<and> 
        ((x = Skip \<and> y = Skip \<and> ((\<sigma>g, \<sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> (Q!?i)) \<or> 
         (x = Throw \<and> y = Throw \<and> ((\<sigma>g, \<sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> (A!?i)) \<or>
         (\<exists>f. x = Fault f \<and>  y = Fault f) \<or> (x = Stuck \<and> y = Stuck)))"             
    apply (rule sim_final[OF sim[simplified xx_def]])
    using snoc h0 apply auto[5] 
    using a6 a6' a6'' snoc(9) a17 a10 a0' a2 a1  Rel_wf_mon[of "((length Rels\<^sub>c)-1)"] by force+            
  then obtain \<Sigma>g' \<Sigma>ls' y where step:"
       (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
        (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> ((Guas\<^sub>c ! ?i), ((Guas\<^sub>s ! ?i))\<^sup>*)\<^sub>\<alpha> \<and> 
        (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S , \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[?i:=y], \<Sigma>g',\<Sigma>ls') \<and> 
        ((x = Skip \<and> y = Skip \<and> ((\<sigma>g, \<sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> (Q!?i)) \<or> 
         (x = Throw \<and> y = Throw \<and> ((\<sigma>g, \<sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> (A!?i)) \<or>
         (\<exists>f. x = Fault f \<and>  y = Fault f) \<or> (x = Stuck \<and> y = Stuck)))"
    by auto 
  then have xy:"x = Skip \<and> y = Skip \<or> x = Throw \<and> y = Throw" using h0  by auto
  have "?i < length \<Sigma>ls'"
  proof-
    show ?thesis using a6 a0' snoc(9) step unfolding related_transitions_def Rel_wf_def by auto
  qed
  have sim_i:"\<forall>i<length xs.
     (\<Gamma>\<^sub>c,(xs ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
       \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i Q\<^sub>;\<^sub>xx i A\<^sub>)
     (\<Gamma>\<^sub>s,(S ! i, toSeqState i (\<Sigma>g', \<Sigma>ls')),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))"
    using sim_i[OF _ snoc(4) a0' snoc(9) a0 a1 a2 snoc(1) snoc(6) a17 a6 a6' a6'' a7 a8] step
           eq_length_pev_tran_step'
    by fast
  have 
   h2:"\<forall>i<length xs. (\<Gamma>\<^sub>c,(xs ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
      \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i ?Q\<^sub>;\<^sub>xx i ?A\<^sub>)
      (\<Gamma>\<^sub>s,(?S ! i, toSeqState i (\<Sigma>g', \<Sigma>ls')),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))"  
    proof-
    {
      fix i
      assume a00:"i<length xs"
      then have "xs!i = (xs@[x])!i" and a00':"i<length (xs)"
        by (auto simp add: l_append)
      moreover have "?Q!i = Q!i" using a00 by auto
      moreover have "?A!i = A!i" using a00 by auto
      moreover have "?S!i = S!i" using a00 by auto        
      ultimately have "(\<Gamma>\<^sub>c,(xs ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
        \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i ?Q\<^sub>;\<^sub>xx i ?A\<^sub>)
        (\<Gamma>\<^sub>s,(?S ! i, toSeqState i (\<Sigma>g', \<Sigma>ls')),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))"
        using sim_i unfolding xx_def by fastforce 
    } thus ?thesis by auto qed    
    have hm:"length \<sigma>ls = length \<Sigma>ls'" using step eq_length_pev_tran_step' snoc(6) by auto
  { assume a00:"throw_program xs"             
    obtain \<Sigma>g'' \<Sigma>ls'' cs' where 
        step2:"(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g', \<Sigma>ls'), \<Sigma>g'', \<Sigma>ls'') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
          (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g', \<Sigma>ls'), \<Sigma>g'', \<Sigma>ls'') \<in> 
               (\<Union> ((!) Guas\<^sub>c ` {..<length ?Q}), (\<Union> ((!) Guas\<^sub>s ` {..<length ?Q}))\<^sup>*)\<^sub>\<alpha> \<and>
           ((\<sigma>g, \<sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> \<Union> ((!) ?A ` {..<length ?Q})  \<and>
           \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
           \<Gamma>\<^sub>s\<turnstile>\<^sub>p (?S, \<Sigma>g', \<Sigma>ls') \<rightarrow>\<^sub>\<tau>\<^sup>* (cs', \<Sigma>g'', \<Sigma>ls'') \<and> throw_program cs'"
     using snoc(2)[OF a00 h2 _ hm h3 h4 h5 h6 h3' h7] step snoc(9)
       unfolding related_transitions_def  by auto
     then have "\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>g'', \<Sigma>ls'') \<and> throw_program c\<^sub>s' "          
       using  p_step_spec_throw[OF _ _ snoc(1,9) xy] step step2 snoc(3) by auto 
    moreover have "(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> 
             (\<Union> ((!) Guas\<^sub>c ` {..<length Q}), (\<Union> ((!) Guas\<^sub>s ` {..<length Q}))\<^sup>*)\<^sub>\<alpha>"
      using tran_in_Guar[OF _ _ snoc(1,8,9)] step step2  by fastforce  
    moreover have "((\<sigma>g, \<sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> \<Union> ((!) A ` {..<length Q})"       
      using step step2 snoc(9) by auto    
    moreover have "(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
      using step step2 unfolding related_transitions_def by auto
    ultimately have 
        "(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
         (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> 
             (\<Union> ((!) Guas\<^sub>c ` {..<length Q}), (\<Union> ((!) Guas\<^sub>s ` {..<length Q}))\<^sup>*)\<^sub>\<alpha> \<and>
           ((\<sigma>g, \<sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> \<Union> ((!) A ` {..<length Q})  \<and>
           \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
           (\<exists>c\<^sub>s'.
               \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>g'', \<Sigma>ls'') \<and> throw_program c\<^sub>s')"
      using step step2 by auto
    then have ?case using snoc(9) by auto
  }
  moreover{
    assume a00:"\<not> throw_program xs"         
    then have a00:"\<forall>i<length xs. xs!i=Skip"  using snoc(3)
      unfolding throw_program_def       
      by (metis (no_types, hide_lams) add_Suc_right append_Nil2 
              l_append length_Cons length_append less_Suc_eq)   
    then have x:"x=Throw" using snoc(3) unfolding throw_program_def apply auto
      by (metis (no_types) l_append nat_neq_iff not_less_eq nth_append_length)   
    then have y:"y = Throw" using xy by auto
    obtain \<Sigma>g'' \<Sigma>ls'' cs' where step2:
     "(((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g', \<Sigma>ls'), \<Sigma>g'', \<Sigma>ls'') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
               (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g', \<Sigma>ls'), \<Sigma>g'', \<Sigma>ls'') \<in> 
                   ((\<Union>j<length ?Q. (Guas\<^sub>c !j)), (\<Union>j<length ?Q. (Guas\<^sub>s ! j))\<^sup>*)\<^sub>\<alpha> \<and>
                 ((\<sigma>g, \<sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> (\<Inter>i<length ?Q.  (?Q ! i)) \<and> \<gamma>\<^sub>n \<subseteq> \<alpha> \<and>
              (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (?S, (\<Sigma>g', \<Sigma>ls')) \<rightarrow>\<^sub>\<tau>\<^sup>* (cs', \<Sigma>g'', \<Sigma>ls'') \<and>
                    (\<forall>i<length cs'. cs' ! i = LanguageCon.com.Skip) \<and> cs' \<noteq> [])"
      using sim_final_skip[OF a0' h5 h4 a0 a1 a2  a6 a6' 
                           a6'' a7 a8 a00 a10 a11 snoc(1) h2 _ _ a17 h3' h6] step hm
      by (auto simp add: related_transitions_def)             
    have "\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>g'', \<Sigma>ls'') \<and> throw_program c\<^sub>s' " 
      apply(rule p_step_spec_throw1[OF _ _  snoc(1,9)]) 
      using step x y apply fast using step2 by auto
      
    moreover have "(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> 
             (\<Union> ((!) Guas\<^sub>c ` {..<length Q}), (\<Union> ((!) Guas\<^sub>s ` {..<length Q}))\<^sup>*)\<^sub>\<alpha>"
      using tran_in_Guar[OF _ _ snoc(1,8,9)] step step2 by fast  
    moreover have "((\<sigma>g, \<sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> \<Union> ((!) A ` {..<length A})"              
      apply (rule tran_in_A[OF _ _ _ a0 ])
      using step step2 snoc(8,9) apply simp 
      using snoc(8,9) apply auto[1] 
      using a0' snoc(12) snoc(9) step2 x y step by auto
    moreover have "(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
      using step step2 unfolding related_transitions_def by auto
    ultimately have 
        "(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
         (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> 
             (\<Union> ((!) Guas\<^sub>c ` {..<length Q}), (\<Union> ((!) Guas\<^sub>s ` {..<length Q}))\<^sup>*)\<^sub>\<alpha> \<and>
           ((\<sigma>g, \<sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> \<Union> ((!) A ` {..<length Q})  \<and>
           \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
           (\<exists>c\<^sub>s'.
               \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>g'', \<Sigma>ls'') \<and> throw_program c\<^sub>s')"
      using a11 snoc(9) by auto
    then have ?case using snoc(9) by auto
  }
  ultimately show ?case using snoc(9) by auto  
qed
 
lemma sim_final_error: assumes 
  a0':"length Rels\<^sub>c = length Guas\<^sub>c \<and>
         length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s " and
  a01:"length PostsA = length PostsQ \<and> length PostsQ = length S \<and> 
       length PostsQ = length C \<and> length C \<le> length Rels\<^sub>c" and
  a0''':"length PostsQ >0" and
  a0:"\<forall>i<length Rels\<^sub>c.
       R\<^sub>c \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. (Guas\<^sub>c ! j)) \<subseteq> (Rels\<^sub>c ! i) \<and>
       R\<^sub>s \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. (Guas\<^sub>s ! j)) \<subseteq> (Rels\<^sub>s!i)" and
  a1:" (\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)) \<subseteq> G\<^sub>c" and
  a2:" (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s ! j)) \<subseteq> G\<^sub>s" and               
  a6:"Rel_wf  ((length Rels\<^sub>c)-1) \<alpha>" and a6':"Rel_wf ((length Rels\<^sub>c)-1) G\<^sub>c" and a6'':"Rel_wf ((length Rels\<^sub>c)-1) G\<^sub>s" and
  a7:"\<forall>i<length Rels\<^sub>c. Rel_wf ((length Rels\<^sub>c)-1) (Rels\<^sub>s ! i)" and
  a8:"\<forall>i<length Rels\<^sub>c. Rel_wf ((length Rels\<^sub>c)-1) (Rels\<^sub>c ! i)" and
  a9:"final_error C" and a9':"C\<noteq>[]" and
  a10:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a11:"\<gamma>\<^sub>a \<subseteq> \<alpha>" and 
  a13:"\<forall>i<length C. 
        (\<Gamma>\<^sub>c, (C ! i,toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c !i), Seq_rel i (Guas\<^sub>c!i)) 
                 \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>) 
        (\<Gamma>\<^sub>s,(S! i,toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s!i), Seq_rel i (Guas\<^sub>s !i))" and
  a15:"((\<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls)) \<in> \<alpha>" and a16:"length \<sigma>ls  = length \<Sigma>ls" and a17:"length Rels\<^sub>c = length \<sigma>ls" and 
  a20:"\<forall>i<length PostsQ. Rel_wf i (PostsA ! i)" and  a20':"\<forall>i<length PostsQ. Rel_wf i (PostsQ ! i)" and
  a21:"\<forall>i<length PostsQ. Sta\<^sub>s (PostsQ!i) ((Rels\<^sub>c!i), ((Rels\<^sub>s!i)\<^sup>*))\<^sub>\<alpha>" and
  a22:"\<forall>i<length PostsQ. Sta\<^sub>s (PostsA!i) ((Rels\<^sub>c!i), ((Rels\<^sub>s!i)\<^sup>*))\<^sub>\<alpha>" 
shows "\<exists>ab bb. (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>              
                (\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', ab, bb) \<and> final_error_r C c\<^sub>s')"
  using  a9' a9 a13  a15 a16  a20 a0''' a01 a21 a20' a22
proof(induction arbitrary:  S  \<Sigma>g \<Sigma>ls PostsQ PostsA  rule:rev_nonempty_induct)
  case (single x S  \<Sigma>g \<Sigma>ls Q A)    
  have h:"\<exists>ab bb y.
          (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> ((Guas\<^sub>c !0, (Guas\<^sub>s !0)\<^sup>*)\<^sub>\<alpha>) \<and>          
          (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S , \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[0:=y], ab, bb)) \<and> 
          ((x = Skip \<and> y = Skip \<and> ((\<sigma>g, \<sigma>ls), ab, bb) \<in> Q!0) \<or> 
           (x = Throw \<and> y = Throw \<and> ((\<sigma>g, \<sigma>ls), ab, bb) \<in> A!0) \<or> 
           (\<exists>f. x = Fault f \<and>  y = Fault f) \<or> (x = Stuck \<and> y = Stuck))"
    apply (rule sim_final) 
    using single final_error_1_D[OF single(1)]  
                  apply (auto simp add: xx_def)[6]
    using Rel_wf_mon a6 a6' a6'' apply auto[3] 
    using a1 a2 single(6,7) a0' a17
         apply (fastforce, fastforce,fastforce)    
    using a10 single(6, 7) a17 by auto
  then  obtain \<Sigma>g' \<Sigma>ls' y where 
  h:"(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g', \<Sigma>ls') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
     (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S , \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[0:=y], \<Sigma>g', \<Sigma>ls')) \<and> 
     ((\<exists>f. x = Fault f \<and>  y = Fault f) \<or> (x = Stuck \<and> y = Stuck))"
    using final_error_1_D[OF single(1)] by auto
  then have 
    "(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g', \<Sigma>ls') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
     (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S , \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* ([y], \<Sigma>g', \<Sigma>ls'))" and 
      "final_error_r [x] [y]"    
    apply (metis (no_types) length_0_conv   single(7) length_Cons list.exhaust 
              list_update_code(2) nat.inject)
    using h by (auto intro:final_error_singleI)
  then show ?case using single(1) by auto
next
  case (snoc x xs  S \<Sigma>g \<Sigma>ls Q A)
  let ?i = "length (xs@[x]) - 1"
  let ?Q = "take (length xs) Q"
  let ?A = "take (length xs) A" 
  let ?S = "take (length xs) S"
  have h0:"x = Skip \<or> x = Throw \<or> x = Stuck \<or> (\<exists>f. x = Fault f)"
    using snoc(3) final_errorD by auto  
  have h3:"\<forall>i<length ?Q. Sim_Rules.Rel_wf i (?A ! i)" 
    using snoc(7) by auto
  have h3':"\<forall>i<length ?Q. Sim_Rules.Rel_wf i (?Q ! i)"
    using snoc(11) snoc(9) by auto
  have h4:"0 < length ?Q" using snoc by auto
  have h5:"length ?A = length ?Q \<and>
     length ?Q = length ?S \<and> length ?Q = length xs \<and> length xs \<le> length Rels\<^sub>c"
    using snoc(9) by auto
  have h6:" \<forall>i<length ?Q. Sta\<^sub>s (?Q ! i) 
                            ((Rels\<^sub>c ! i),((Rels\<^sub>s ! i)\<^sup>*))\<^sub>\<alpha>"
    using snoc(10) by auto  
  have h7:" \<forall>i<length ?Q. Sta\<^sub>s (?A ! i) 
                            ((Rels\<^sub>c ! i),((Rels\<^sub>s ! i)\<^sup>*))\<^sub>\<alpha>"
    using snoc(12) by auto
  have sim:"(\<Gamma>\<^sub>c,(x, toSeqState ?i (\<sigma>g, \<sigma>ls)),Seq_rel ?i (Rels\<^sub>c ! ?i),Seq_rel ?i (Guas\<^sub>c ! ?i))
     \<succeq>\<^sub>(\<^sub>Seq_rel ?i \<alpha>\<^sub>;\<^sub>xx ?i Q\<^sub>;\<^sub>xx ?i A\<^sub>)
     (\<Gamma>\<^sub>s,(S ! ?i, toSeqState ?i (\<Sigma>g, \<Sigma>ls)),Seq_rel ?i (Rels\<^sub>s ! ?i),Seq_rel ?i (Guas\<^sub>s ! ?i))" 
      using x snoc(4,3,8,9) by auto  
  have "\<exists>\<Sigma>g' \<Sigma>ls' y. 
       (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
        (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> ((Guas\<^sub>c ! ?i), ((Guas\<^sub>s ! ?i))\<^sup>*)\<^sub>\<alpha> \<and> 
        (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S , \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[?i:=y], \<Sigma>g',\<Sigma>ls') \<and> 
        ((x = Skip \<and> y = Skip \<and> ((\<sigma>g, \<sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> (Q!?i)) \<or> 
         (x = Throw \<and> y = Throw \<and> ((\<sigma>g, \<sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> (A!?i)) \<or>
         (\<exists>f. x = Fault f \<and>  y = Fault f) \<or> (x = Stuck \<and> y = Stuck)))"             
    apply (rule sim_final[OF sim[simplified xx_def]])
    using snoc h0 apply auto[5] 
    using a6 a6' a6'' snoc(9) a17 a10 a0' a2 a1  Rel_wf_mon[of "((length Rels\<^sub>c)-1)"] by force+            
  then obtain \<Sigma>g' \<Sigma>ls' y where step:"
       (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
        (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> ((Guas\<^sub>c ! ?i), ((Guas\<^sub>s ! ?i))\<^sup>*)\<^sub>\<alpha> \<and> 
        (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (S , \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (S[?i:=y], \<Sigma>g',\<Sigma>ls') \<and> 
        ((x = Skip \<and> y = Skip \<and> ((\<sigma>g, \<sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> (Q!?i)) \<or> 
         (x = Throw \<and> y = Throw \<and> ((\<sigma>g, \<sigma>ls), \<Sigma>g',\<Sigma>ls') \<in> (A!?i)) \<or>
         (\<exists>f. x = Fault f \<and>  y = Fault f) \<or> (x = Stuck \<and> y = Stuck)))"
    by auto 
  have "?i < length \<Sigma>ls'"
  proof-
    show ?thesis using a6 a0' snoc(9) step unfolding related_transitions_def Rel_wf_def by auto
  qed
  have sim_i:"\<forall>i<length xs.
     (\<Gamma>\<^sub>c,(xs ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
       \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i Q\<^sub>;\<^sub>xx i A\<^sub>)
     (\<Gamma>\<^sub>s,(S ! i, toSeqState i (\<Sigma>g', \<Sigma>ls')),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))"
    using sim_i[OF _ snoc(4) a0' snoc(9) a0 a1 a2 snoc(1) snoc(6) a17 a6 a6' a6'' a7 a8] step
           eq_length_pev_tran_step'
    by fast
  have 
   h2:"\<forall>i<length xs. (\<Gamma>\<^sub>c,(xs ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
      \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i ?Q\<^sub>;\<^sub>xx i ?A\<^sub>)
      (\<Gamma>\<^sub>s,(?S ! i, toSeqState i (\<Sigma>g', \<Sigma>ls')),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))"  
  proof-
  {
    fix i
    assume a00:"i<length xs"
    then have "xs!i = (xs@[x])!i" and a00':"i<length (xs)"
      by (auto simp add: l_append)
    moreover have "?Q!i = Q!i" using a00 by auto
    moreover have "?A!i = A!i" using a00 by auto
    moreover have "?S!i = S!i" using a00 by auto        
    ultimately have "(\<Gamma>\<^sub>c,(xs ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
      \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i ?Q\<^sub>;\<^sub>xx i ?A\<^sub>)
      (\<Gamma>\<^sub>s,(?S ! i, toSeqState i (\<Sigma>g', \<Sigma>ls')),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))"
      using sim_i unfolding xx_def by fastforce 
  } thus ?thesis by auto qed    
  have hm:"length \<sigma>ls = length \<Sigma>ls'" using step eq_length_pev_tran_step' snoc(6) by auto
  { assume a00:"final_error xs" 
    obtain \<Sigma>g'' \<Sigma>ls'' cs' where 
      step2:"(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g', \<Sigma>ls'), \<Sigma>g'', \<Sigma>ls'') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>          
         \<Gamma>\<^sub>s\<turnstile>\<^sub>p (?S, \<Sigma>g', \<Sigma>ls') \<rightarrow>\<^sub>\<tau>\<^sup>* (cs', \<Sigma>g'', \<Sigma>ls'') \<and> final_error_r xs cs'"
      using snoc(2)[OF a00 h2 _ hm h3 h4 h5 h6 h3' h7] step snoc(9)
      unfolding related_transitions_def  by auto          
    then have "final_error cs'" using a00 using final_error_r_def by blast
    then have "\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>g'', \<Sigma>ls'') \<and> final_error_r (xs@[x]) c\<^sub>s' "                 
      using  p_step_spec_error[OF _ _ snoc(1) _ snoc(9) ] step step2 snoc(3) by auto 
    moreover have "(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
      using step step2 unfolding related_transitions_def by auto
    ultimately have ?case by auto
  }
  moreover{
    assume a00:"\<not> final_error xs"         
    then have a00':"\<forall>i<length xs. xs!i=Skip \<or> xs!i = Throw"  using snoc(3)
      using final_error_skip_throw by blast    
    have x:"x=Stuck \<and> y=Stuck \<or> (\<exists>f. x=Fault f \<and> y = Fault f)" using  snoc(3) a00 step
      using final_error_stuck_fault by blast
    { assume a00:"\<forall>i<length xs. xs!i = Skip" 
      obtain \<Sigma>g'' \<Sigma>ls'' cs' where step2:
      "(((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g', \<Sigma>ls'), \<Sigma>g'', \<Sigma>ls'') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
               (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g', \<Sigma>ls'), \<Sigma>g'', \<Sigma>ls'') \<in> 
                   ((\<Union>j<length ?Q. (Guas\<^sub>c !j)), (\<Union>j<length ?Q. (Guas\<^sub>s ! j))\<^sup>*)\<^sub>\<alpha> \<and>
                 ((\<sigma>g, \<sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> (\<Inter>i<length ?Q.  (?Q ! i)) \<and> \<gamma>\<^sub>n \<subseteq> \<alpha> \<and>
              (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (?S, (\<Sigma>g', \<Sigma>ls')) \<rightarrow>\<^sub>\<tau>\<^sup>* (cs', \<Sigma>g'', \<Sigma>ls'') \<and>
                    (\<forall>i<length cs'. cs' ! i = LanguageCon.com.Skip) \<and> cs' \<noteq> [])"         
        using sim_final_skip[OF a0' h5 h4 a0 a1 a2  a6 a6'
                           a6'' a7 a8 a00 a10 a11 snoc(1) h2 _ _ a17 h3' h6] step hm
        by (auto simp add: related_transitions_def)  
      then have cs'_throw_skip:"\<forall>i<length cs'. cs' ! i = Skip \<or> cs' ! i = Throw" 
        by auto
      have "\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>g'', \<Sigma>ls'') \<and> final_error_r (xs@[x]) c\<^sub>s'" 
        apply(rule p_step_spec_error1[OF _ _  snoc(1) cs'_throw_skip a00' snoc(9) x]) 
        using step  step2 by auto
      moreover have "(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
        using step step2 unfolding related_transitions_def by auto
      ultimately have ?case using step by auto
    }
    moreover{
      assume "\<not>(\<forall>i<length xs. xs!i = Skip)" 
      then have a00:"throw_program xs" using a00' unfolding throw_program_def by auto
      obtain \<Sigma>g'' \<Sigma>ls'' cs' where step2:
      "(((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g', \<Sigma>ls'), \<Sigma>g'', \<Sigma>ls'') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
               (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g', \<Sigma>ls'), \<Sigma>g'', \<Sigma>ls'') \<in> 
                   ((\<Union>j<length ?Q. (Guas\<^sub>c !j)), (\<Union>j<length ?Q. (Guas\<^sub>s ! j))\<^sup>*)\<^sub>\<alpha> \<and>
                 ((\<sigma>g, \<sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> (\<Union>i<length ?A.  (?A ! i)) \<and> \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
              (\<Gamma>\<^sub>s\<turnstile>\<^sub>p (?S, (\<Sigma>g', \<Sigma>ls')) \<rightarrow>\<^sub>\<tau>\<^sup>* (cs', \<Sigma>g'', \<Sigma>ls'') \<and> throw_program cs')"         
        using sim_final_throw[OF a0' h5 h4 a0 a1 a2  a6 a6'
                           a6'' a7 a8 a00 snoc(1) a10 a11  h2 _ _ a17 h3 h3' h6 h7] step hm
        by (auto simp add: related_transitions_def)        
      have "\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (S, \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>g'', \<Sigma>ls'') \<and> final_error_r (xs@[x]) c\<^sub>s'" 
        apply(rule p_step_spec_error1[OF _ _  snoc(1) _ a00' snoc(9) x]) 
        using step  step2 unfolding throw_program_def by auto
      moreover have "(((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), \<Sigma>g'', \<Sigma>ls'') \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
        using step step2 unfolding related_transitions_def by auto
      ultimately have ?case using step by auto
    }
    ultimately have ?case by auto  
  }
     
  ultimately show ?case using snoc(9) by auto  
qed

lemma sim_comp_sound1:
  assumes    
    a0':"length Rels\<^sub>c = length Guas\<^sub>c \<and> length Rels\<^sub>c = length PostsQ \<and> length Rels\<^sub>c = length PostsA \<and>
         length Rels\<^sub>c = length Guas\<^sub>s \<and> length Rels\<^sub>c = length Rels\<^sub>s " and
    a0'':"length Rels\<^sub>c = length Coms\<^sub>s \<and> length Rels\<^sub>c = length Coms\<^sub>c" and
    a0''':"length Rels\<^sub>c >0" and
    a0:"\<forall>i<length Rels\<^sub>c.
       R\<^sub>c \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>c \<and> j \<noteq> i}. (Guas\<^sub>c ! j)) \<subseteq> (Rels\<^sub>c ! i) \<and>
       R\<^sub>s \<union> (\<Union>j\<in>{j. j < length Guas\<^sub>s \<and> j \<noteq> i}. (Guas\<^sub>s ! j)) \<subseteq> (Rels\<^sub>s!i)" and
 a1:" (\<Union>j<length Guas\<^sub>c. (Guas\<^sub>c !j)) \<subseteq> G\<^sub>c" and
 a2:" (\<Union>j<length Guas\<^sub>s. (Guas\<^sub>s ! j)) \<subseteq> G\<^sub>s" and             
 a3:" (\<Inter>i<length PostsQ.  (PostsQ ! i)) \<subseteq> \<gamma>\<^sub>n" and
 a4:" (\<Union>i<length PostsA.  (PostsA ! i)) \<subseteq> \<gamma>\<^sub>a " and 
 a5:" \<forall>i<length PostsQ.                                                          
       (\<Gamma>\<^sub>c, (Coms\<^sub>c ! i,toSeqState i \<sigma>),Seq_rel i (Rels\<^sub>c !i), Seq_rel i (Guas\<^sub>c!i)) 
          \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>) 
       (\<Gamma>\<^sub>s,(Coms\<^sub>s! i,toSeqState i \<Sigma>),Seq_rel i (Rels\<^sub>s!i), Seq_rel i (Guas\<^sub>s !i))" and
 a8:"\<forall>i<length PostsA. Sta\<^sub>s (PostsA!i) ((Rels\<^sub>c!i), ((Rels\<^sub>s!i)\<^sup>*))\<^sub>\<alpha>" and
 a9:"\<forall>i<length PostsQ. Sta\<^sub>s (PostsQ!i) ((Rels\<^sub>c!i), ((Rels\<^sub>s!i)\<^sup>*))\<^sub>\<alpha>" and  
 a10:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a11:"\<gamma>\<^sub>a \<subseteq> \<alpha>" and 
 a12:"\<forall>i<length PostsQ. \<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow>(\<sigma>,\<sigma>)\<in> (Guas\<^sub>c ! i)" and 
 a13:"length PostsQ = length (snd \<sigma>)" and a14:"length PostsQ = length (snd \<Sigma>)" and 
 a15:"R_wf (length PostsQ) \<alpha>" and a16:"R_wf (length PostsQ) G\<^sub>c" and a17:"R_wf (length PostsQ) G\<^sub>s" and
 a20:"\<forall>i<length PostsQ. R_wf (length PostsQ) (Rels\<^sub>s ! i)" and
 a21:"\<forall>i<length PostsQ. R_wf (length PostsQ) (Rels\<^sub>c ! i)" and 
 a22:"\<forall>i<length PostsQ. R_wf (length PostsQ) (PostsQ ! i)" and 
 a23:"\<forall>i<length PostsQ. R_wf (length PostsQ) (PostsA ! i)"
shows "(\<Gamma>\<^sub>c,(Coms\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Coms\<^sub>s,\<Sigma>),R\<^sub>s,G\<^sub>s)" 
  using a5 a0'' a13 a14 
proof (coinduction arbitrary:\<sigma> \<Sigma> Coms\<^sub>c Coms\<^sub>s,clarsimp)  
  fix \<sigma>g \<sigma>ls \<Sigma>g \<Sigma>ls Coms\<^sub>c' Coms\<^sub>s'
  assume a5:
   "\<forall>i<length \<sigma>ls. 
      (\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i)) 
         \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
      (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i, toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" and
  a01:"length \<Sigma>ls = length \<sigma>ls" and a02:"length PostsQ = length \<sigma>ls" and
  a0'': "length Coms\<^sub>c' = length Coms\<^sub>s'" and
  a01'':"length Rels\<^sub>c = length Coms\<^sub>s'" 
  have R_wf_Rc:"R_wf (length PostsQ) R\<^sub>c" 
  proof- 
    have "R\<^sub>c \<subseteq> Rels\<^sub>c !0" using a0 a0'''  by auto
    moreover have "R_wf (length PostsQ) (Rels\<^sub>c !0)" using a21 a0''' a0' by auto
    ultimately show ?thesis using R_wf_subset by auto
  qed
  have R_wf_Rs:"R_wf (length PostsQ) R\<^sub>s" 
  proof- 
    have "R\<^sub>s \<subseteq> Rels\<^sub>s !0" using a0 a0'''  by auto
    moreover have "R_wf (length PostsQ) (Rels\<^sub>s !0)" using a20 a0''' a0' by auto
    ultimately show ?thesis using R_wf_subset by auto
  qed
  have 
    a18:"\<forall>i<length PostsQ. R_wf (length PostsQ) (Guas\<^sub>c ! i)" and 
    a19:"\<forall>i<length PostsQ. R_wf (length PostsQ) (Guas\<^sub>s ! i)"
     apply auto  using a0' a1 a16 unfolding R_wf_def apply fastforce
     using a0' a2 a17 unfolding R_wf_def by fastforce     
  have a5':
    "\<forall>i<length PostsQ.   
      (\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i)) 
         \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
      (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i, toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))"
    using a5 a0'' a01'' a0' a02 by auto  
  moreover have alpha:"((\<sigma>g,\<sigma>ls), (\<Sigma>g,\<Sigma>ls)) \<in> \<alpha>"
  proof-              
     have "(toSeqState 0 (\<sigma>g,\<sigma>ls), toSeqState 0 (\<Sigma>g,\<Sigma>ls)) \<in> Seq_rel 0 \<alpha>"
      using  dest_sim_alpha a0' a0'''   a01'' a5' 
      by metis               
    then show ?thesis using a15 unfolding toSeqState_def 
         Seq_rel_def Let_def split_beta R_wf_def  apply auto
      by (metis Cons_nth_drop_Suc a0' a0''' a01  a02 drop0)      
  qed
(*  moreover have a02:"length PostsQ = length (\<sigma>ls)" using  alpha a15 unfolding R_wf_def by auto
  moreover have a01:"length \<Sigma>ls = length \<sigma>ls" using alpha a15 unfolding R_wf_def by auto *)
  moreover 
  { fix c\<^sub>c' \<sigma>'g \<sigma>'ls
    assume b01:"\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>\<tau> (Coms\<^sub>c', (\<sigma>g,\<sigma>ls)) \<rightarrow> (c\<^sub>c',  (\<sigma>'g,\<sigma>'ls))"
    then obtain i c' where "i< length Coms\<^sub>c' \<and>  
                            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> ((Coms\<^sub>c'!i), toSeqPar  i (\<sigma>g,\<sigma>ls)) \<rightarrow> (c',  toSeqPar i (\<sigma>'g,\<sigma>'ls)) \<and>
                            (\<forall>j. j\<noteq>i \<longrightarrow> c\<^sub>c'!j = (Coms\<^sub>c'!j)) \<and> c\<^sub>c'!i=c' \<and> (\<forall>j\<noteq>i. \<sigma>'ls ! j = \<sigma>ls ! j) \<and> 
                       length \<sigma>'ls = length \<sigma>ls"
      apply clarsimp apply (rule step_pev_pair_elim_cases[OF b01]) using a0' a0'' a01'' a02
      by (metis eq_snd_iff fstI length_list_update nth_list_update_eq nth_list_update_neq)      
    then have step:"i< length Coms\<^sub>c' \<and>  
                    \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> ((Coms\<^sub>c'!i), CRef.toSeq (toSeqState i (\<sigma>g, \<sigma>ls))) \<rightarrow>
                          (c', CRef.toSeq ((\<sigma>'g, (\<sigma>'ls!i)), snd (toSeqState i (\<sigma>g, \<sigma>ls)))) \<and>
                    (\<forall>j. j\<noteq>i \<longrightarrow> c\<^sub>c'!j = (Coms\<^sub>c'!j)) \<and> c\<^sub>c'!i=c' \<and> (\<forall>j\<noteq>i. \<sigma>'ls ! j = \<sigma>ls ! j) \<and>
                    length \<sigma>'ls = length \<sigma>ls"
      unfolding toSeq_def toSeqState_def by auto
    then have sim:
      "(\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i)) 
          \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
       (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i, toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" 
      using a5 a0' a0'' a01''
      by (simp add: a5') 
    have i_len:"i<length PostsQ" using a5 a0' a0'' a01'' step by auto   
    obtain c\<^sub>s' \<Sigma>'g \<Sigma>'ls where alpha_rel_guar:
      "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Coms\<^sub>s' ! i, CRef.toSeq (toSeqState i (\<Sigma>g, \<Sigma>ls))) \<rightarrow>\<^sub>\<tau>\<^sup>*
            (c\<^sub>s', CRef.toSeq ((\<Sigma>'g, \<Sigma>'ls), snd (toSeqState i (\<Sigma>g, \<Sigma>ls)))) \<and>
        (((\<sigma>'g, (\<sigma>'ls!i)), snd (toSeqState i (\<sigma>g, \<sigma>ls))), (\<Sigma>'g, \<Sigma>'ls), 
           snd (toSeqState i (\<Sigma>g, \<Sigma>ls))) \<in> Seq_rel i \<alpha> \<and>
        ((toSeqState i (\<sigma>g, \<sigma>ls), (\<sigma>'g, (\<sigma>'ls!i)), snd (toSeqState i (\<sigma>g, \<sigma>ls))), 
           toSeqState i (\<Sigma>g, \<Sigma>ls), (\<Sigma>'g, \<Sigma>'ls), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))) 
            \<in> ((Seq_rel i (Guas\<^sub>c ! i), (Seq_rel i (Guas\<^sub>s ! i))\<^sup>*)\<^sub>(Seq_rel i \<alpha>)) \<and>
         (\<Gamma>\<^sub>c,(c', (\<sigma>'g, (\<sigma>'ls!i)), snd (toSeqState i (\<sigma>g, \<sigma>ls))),
                Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
             (\<Gamma>\<^sub>s,(c\<^sub>s', (\<Sigma>'g, \<Sigma>'ls), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))),
                Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" 
      using  step apply clarify by (rule sim_elim_cases[OF sim], force)   
    obtain \<Sigma>'g1 \<Sigma>'ls1 
      where eq_\<Sigma>_par:"(\<Sigma>'g1, \<Sigma>'ls1) = (toPar i (\<Sigma>'g, \<Sigma>'ls) (\<Sigma>g, \<Sigma>ls))"
      by auto    
    have eq_toseq\<sigma>':"toSeqState i (\<sigma>'g, (\<sigma>'ls)) = ((\<sigma>'g, (\<sigma>'ls!i)), snd (toSeqState i (\<sigma>g, \<sigma>ls)))"
        using step unfolding toSeqState_def Let_def split_beta apply auto
        apply (metis a0' a0'' a01'' a02 append_eq_append_conv eq_list_i length_take)
        by (metis a0' a0'' a01'' a02 append_eq_append_conv eq_list_i length_drop)
    have eq_toseq\<Sigma>':"toSeqState i (toPar i (\<Sigma>'g, \<Sigma>'ls) (\<Sigma>g, \<Sigma>ls)) = 
                     ((\<Sigma>'g, \<Sigma>'ls), snd (toSeqState i (\<Sigma>g, \<Sigma>ls)))"
        unfolding toSeqState_def apply auto
        by (metis a0' a0'' a01 a01'' a02 local.step nth_list_update_eq) 
    have alpha_rel_guar':"(toSeqState i (\<sigma>'g, \<sigma>'ls), toSeqState i (\<Sigma>'g1, \<Sigma>'ls1)) \<in> Seq_rel i \<alpha> \<and>
     ((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>'g, \<sigma>'ls)), toSeqState i (\<Sigma>g, \<Sigma>ls), toSeqState i (\<Sigma>'g1, \<Sigma>'ls1))
     \<in> (Seq_rel i (Guas\<^sub>c ! i), (Seq_rel i (Guas\<^sub>s ! i))\<^sup>*)\<^sub>Seq_rel i \<alpha> \<and>
     (\<Gamma>\<^sub>c,(c', toSeqState i (\<sigma>'g, \<sigma>'ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
     \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
     (\<Gamma>\<^sub>s,(c\<^sub>s', toSeqState i (\<Sigma>'g1, \<Sigma>'ls1)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" 
       using alpha_rel_guar eq_\<Sigma>_par eq_toseq\<Sigma>' eq_toseq\<sigma>' by auto
    have "((\<sigma>'g, \<sigma>'ls), (toPar i (\<Sigma>'g, \<Sigma>'ls) (\<Sigma>g, \<Sigma>ls))) \<in> \<alpha>"
    proof-                   
      have "(toSeqState i (\<sigma>'g, (\<sigma>'ls)), toSeqState i (toPar i (\<Sigma>'g, \<Sigma>'ls) (\<Sigma>g, \<Sigma>ls))) 
         \<in> Seq_rel i \<alpha>"
        using alpha_rel_guar eq_toseq\<sigma>' eq_toseq\<Sigma>'
        by fastforce     
      moreover have "R_wf (length (snd (toPar i (\<Sigma>'g, \<Sigma>'ls) (\<Sigma>g, \<Sigma>ls)))) \<alpha>"
      proof-
        have "length (snd (toPar i (\<Sigma>'g, \<Sigma>'ls) (\<Sigma>g, \<Sigma>ls))) = length \<Sigma>ls"
          by auto
        also have "R_wf (length \<Sigma>ls) \<alpha>"
          using a01 a02 a15 by auto
        finally show ?thesis by auto
      qed
      ultimately show ?thesis using Seq_rel_par
        using R_wf_def a02 alpha i_len local.step by fastforce
    qed
    then have "((\<sigma>'g, \<sigma>'ls), \<Sigma>'g1,\<Sigma>'ls1) \<in> \<alpha>" using eq_\<Sigma>_par by auto
    moreover have step_par_s:
      "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Coms\<^sub>s'[i:=c\<^sub>s'], toPar i (\<Sigma>'g, \<Sigma>'ls) (\<Sigma>g, \<Sigma>ls))" 
      using mult_step_in_par1 a0' a01 a01'' a02 alpha_rel_guar a0'' step
    proof- 
       have f3:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Coms\<^sub>s' ! i, toSeqPar i (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', (\<Sigma>'g, \<Sigma>'ls))" 
        using alpha_rel_guar  
        apply (auto simp add: toSeqPar_toSeq_SeqState) by (auto simp add: toSeq_def) 
      then show ?thesis using mult_step_in_par1[OF _ _ f3] 
         mult_step_in_par1 a0' a01 a01'' a02  a0'' step by auto      
    qed
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Coms\<^sub>s'[i:=c\<^sub>s'], \<Sigma>'g1,\<Sigma>'ls1)" using eq_\<Sigma>_par by auto
    moreover have gcs:"(((\<sigma>g,\<sigma>ls), (\<sigma>'g,\<sigma>'ls)), (\<Sigma>g, \<Sigma>ls), 
                        toPar i (\<Sigma>'g, \<Sigma>'ls) (\<Sigma>g, \<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
    proof-
      have i_len:"i<length \<sigma>ls" 
        using a02 i_len step by auto
      moreover have "(((\<sigma>g, \<sigma>ls), \<sigma>'g, \<sigma>'ls), (\<Sigma>g, \<Sigma>ls), fst (toPar i (\<Sigma>'g, \<Sigma>'ls) (\<Sigma>g, \<Sigma>ls)), 
                    snd (toPar i (\<Sigma>'g, \<Sigma>'ls) (\<Sigma>g, \<Sigma>ls))) \<in> (Guas\<^sub>c ! i, (Guas\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha>"
      proof-        
        have eq_len:"
          length \<sigma>'ls = length \<sigma>ls \<and> length \<sigma>ls = length \<Sigma>ls \<and>
          length \<Sigma>ls =  length (snd (toPar i (\<Sigma>'g, \<Sigma>'ls) (\<Sigma>g, \<Sigma>ls)))"
          using step a01 by auto        
         moreover have RF:"R_wf (length \<sigma>ls) (Guas\<^sub>c ! i) \<and> R_wf (length \<sigma>ls) (Guas\<^sub>s ! i)"
           using a16 a17   unfolding R_wf_def apply auto
           by (metis (no_types, hide_lams) UN_subset_iff  lessThan_iff 
                  subsetD  a0'  a0'' a02  a01'' a2 a1 step)+  
         ultimately show ?thesis using eq_toseq\<Sigma>' eq_toseq\<sigma>'
           by (metis  i_len  a02 a15 alpha_rel_guar prod.exhaust_sel rel_tran_seq)
       qed     
       moreover have "Guas\<^sub>c ! i \<subseteq> G\<^sub>c"
         by (metis (no_types) UN_subset_iff i_len a0' a02 a1 lessThan_iff)
       moreover have "Guas\<^sub>s ! i \<subseteq> G\<^sub>s"
         by (metis (no_types) UN_subset_iff i_len a0' a02 a2 lessThan_iff)
       ultimately show ?thesis by (simp add: G_comp1)       
     qed
     then have "(((\<sigma>g,\<sigma>ls), (\<sigma>'g,\<sigma>'ls)), (\<Sigma>g, \<Sigma>ls), \<Sigma>'g1, \<Sigma>'ls1) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
       using eq_\<Sigma>_par by auto
     moreover have 
       "(\<forall>i'<length PostsQ. (\<Gamma>\<^sub>c,(c\<^sub>c' ! i', toSeqState i' (\<sigma>'g,\<sigma>'ls)),
             Seq_rel i' (Rels\<^sub>c ! i'),Seq_rel i' (Guas\<^sub>c ! i')) 
          \<succeq>\<^sub>(\<^sub>Seq_rel i' \<alpha>\<^sub>;\<^sub>xx i' PostsQ\<^sub>;\<^sub>xx i' PostsA\<^sub>)
        (\<Gamma>\<^sub>s,(Coms\<^sub>s'[i:=c\<^sub>s'] ! i', toSeqState i' (\<Sigma>'g1, \<Sigma>'ls1)),
            Seq_rel i' (Rels\<^sub>s ! i'),Seq_rel i' (Guas\<^sub>s ! i')))"  
     proof-
       have aa:"i < length Coms\<^sub>c' \<and> (\<forall>j. j \<noteq> i \<longrightarrow> c\<^sub>c' ! j = Coms\<^sub>c' ! j) \<and> c\<^sub>c' ! i = c'" using step
         by blast    
       have "length \<sigma>ls = length PostsQ" and "length \<sigma>ls = length \<sigma>'ls" and 
              "length \<Sigma>ls = length \<sigma>ls" and len_\<Sigma>':"length \<Sigma>ls = length \<Sigma>'ls1"
         using eq_\<Sigma>_par by (auto simp add: a02 step a01 )       
       then show ?thesis 
         using rest_sim[OF a0 a0' a0''' a5' a0'' a01'' i_len 
               alpha_rel_guar' aa a15 a16 a17 a18 a19 a20 a21] by auto                 
     qed   
     then have "(\<forall>i'<length \<sigma>ls. (\<Gamma>\<^sub>c,(c\<^sub>c' ! i', toSeqState i' (\<sigma>'g,\<sigma>'ls)),
             Seq_rel i' (Rels\<^sub>c ! i'),Seq_rel i' (Guas\<^sub>c ! i')) 
          \<succeq>\<^sub>(\<^sub>Seq_rel i' \<alpha>\<^sub>;\<^sub>xx i' PostsQ\<^sub>;\<^sub>xx i' PostsA\<^sub>)
        (\<Gamma>\<^sub>s,(Coms\<^sub>s'[i:=c\<^sub>s'] ! i', toSeqState i' (\<Sigma>'g1, \<Sigma>'ls1)),
            Seq_rel i' (Rels\<^sub>s ! i'),Seq_rel i' (Guas\<^sub>s ! i')))"  
       using a15 unfolding R_wf_def
       by (metis (no_types, hide_lams) calculation(1)  local.step )                      
     moreover have "length Coms\<^sub>s' = length (Coms\<^sub>s'[i:=c\<^sub>s']) \<and>
                    length Coms\<^sub>s' = length c\<^sub>c' \<and> length \<sigma>ls = length \<sigma>'ls \<and> 
                    length \<sigma>ls = length  \<Sigma>'ls1"
       by (metis (no_types, hide_lams) R_wf_def a0'' a15 b01 
           calculation(1) length_list_update local.step step_pev_pair_elim_cases)       
     ultimately have "\<exists>c\<^sub>s' aa ba.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', aa, ba) \<and>
                ((\<sigma>'g,\<sigma>'ls), aa, ba) \<in> \<alpha> \<and>
                (((\<sigma>g, \<sigma>ls),\<sigma>'g, \<sigma>'ls), (\<Sigma>g, \<Sigma>ls), aa, ba) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                ((\<forall>i<length \<sigma>ls. (\<Gamma>\<^sub>c,(c\<^sub>c' ! i, toSeqState i (\<sigma>'g,\<sigma>'ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                     \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
                     (\<Gamma>\<^sub>s,(c\<^sub>s' ! i, toSeqState i (aa, ba)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))) \<and>
                 length Coms\<^sub>s' = length c\<^sub>s' \<and>
                 length Coms\<^sub>s' = length c\<^sub>c' \<and> length \<sigma>ls = length \<sigma>'ls \<and> length \<sigma>ls = length ba  \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>'g,\<sigma>'ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', aa, ba),R\<^sub>s,G\<^sub>s))" by blast
  } 
  moreover 
  { fix v c\<^sub>c' \<sigma>g' \<sigma>ls'
    assume b01: "\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>(Some v) (Coms\<^sub>c', (\<sigma>g,\<sigma>ls)) \<rightarrow> (c\<^sub>c', (\<sigma>g',\<sigma>ls')) "
    then obtain i c' where "i< length Coms\<^sub>c' \<and>  
                            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) ((Coms\<^sub>c'!i), toSeqPar  i (\<sigma>g,\<sigma>ls)) \<rightarrow> (c',  toSeqPar i (\<sigma>g',\<sigma>ls')) \<and>
                            (\<forall>j. j\<noteq>i \<longrightarrow> c\<^sub>c'!j = (Coms\<^sub>c'!j)) \<and> c\<^sub>c'!i=c' \<and> (\<forall>j\<noteq>i. \<sigma>ls' ! j = \<sigma>ls ! j) \<and> 
                       length \<sigma>ls' = length \<sigma>ls"
      apply clarsimp apply (rule step_pev_pair_elim_cases[OF b01]) using a0' a0'' a01'' a02
      by (metis eq_snd_iff fstI length_list_update nth_list_update_eq nth_list_update_neq)
    then have step:"i< length Coms\<^sub>c' \<and>  
                    \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) ((Coms\<^sub>c'!i), CRef.toSeq (toSeqState i (\<sigma>g, \<sigma>ls))) \<rightarrow>
                          (c', CRef.toSeq ((\<sigma>g', (\<sigma>ls'!i)), snd (toSeqState i (\<sigma>g, \<sigma>ls)))) \<and>
                    (\<forall>j. j\<noteq>i \<longrightarrow> c\<^sub>c'!j = (Coms\<^sub>c'!j)) \<and> c\<^sub>c'!i=c' \<and> (\<forall>j\<noteq>i. \<sigma>ls' ! j = \<sigma>ls ! j) \<and>
                    length \<sigma>ls' = length \<sigma>ls"
      unfolding toSeq_def toSeqState_def by auto
    then have sim:
      "(\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i)) 
          \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
       (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i, toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" 
      using a5 a0' a0'' a01''
      by (simp add: a5')
    have i_len:"i<length PostsQ" using a5 a0' a0'' a01'' step by auto
    obtain c\<^sub>s' \<Sigma>g' \<Sigma>ls' where alpha_rel_guar:
      "\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (Coms\<^sub>s' ! i, CRef.toSeq (toSeqState i (\<Sigma>g, \<Sigma>ls))) \<rightarrow>\<^sup>+
            (c\<^sub>s', CRef.toSeq ((\<Sigma>g', \<Sigma>ls'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls)))) \<and>
        (((\<sigma>g', (\<sigma>ls'!i)), snd (toSeqState i (\<sigma>g, \<sigma>ls))), (\<Sigma>g', \<Sigma>ls'), 
           snd (toSeqState i (\<Sigma>g, \<Sigma>ls))) \<in> Seq_rel i \<alpha> \<and>
        ((toSeqState i (\<sigma>g, \<sigma>ls), (\<sigma>g', (\<sigma>ls'!i)), snd (toSeqState i (\<sigma>g, \<sigma>ls))), 
           toSeqState i (\<Sigma>g, \<Sigma>ls), (\<Sigma>g', \<Sigma>ls'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))) 
            \<in> ((Seq_rel i (Guas\<^sub>c ! i), (Seq_rel i (Guas\<^sub>s ! i))\<^sup>*)\<^sub>(Seq_rel i \<alpha>)) \<and>
         (\<Gamma>\<^sub>c,(c', (\<sigma>g', (\<sigma>ls'!i)), snd (toSeqState i (\<sigma>g, \<sigma>ls))),
                Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
             (\<Gamma>\<^sub>s,(c\<^sub>s', (\<Sigma>g', \<Sigma>ls'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls))),
                Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" 
      using  step apply clarify by (rule sim_elim_cases[OF sim], force)
    obtain \<Sigma>g'1 \<Sigma>ls'1 
      where eq_\<Sigma>_par:"(\<Sigma>g'1, \<Sigma>ls'1) = (toPar i (\<Sigma>g', \<Sigma>ls') (\<Sigma>g, \<Sigma>ls))"
      by auto    
    have eq_toseq\<sigma>':"toSeqState i (\<sigma>g', (\<sigma>ls')) = ((\<sigma>g', (\<sigma>ls'!i)), snd (toSeqState i (\<sigma>g, \<sigma>ls)))"
        using step unfolding toSeqState_def Let_def split_beta apply auto
        apply (metis a0' a0'' a01'' a02 append_eq_append_conv eq_list_i length_take)
        by (metis a0' a0'' a01'' a02 append_eq_append_conv eq_list_i length_drop)
    have eq_toseq\<Sigma>':"toSeqState i (toPar i (\<Sigma>g', \<Sigma>ls') (\<Sigma>g, \<Sigma>ls)) = 
                     ((\<Sigma>g', \<Sigma>ls'), snd (toSeqState i (\<Sigma>g, \<Sigma>ls)))"
        unfolding toSeqState_def apply auto
        by (metis a0' a0'' a01 a01'' a02 local.step nth_list_update_eq) 
    have alpha_rel_guar':"(toSeqState i (\<sigma>g', \<sigma>ls'), toSeqState i (\<Sigma>g'1, \<Sigma>ls'1)) \<in> Seq_rel i \<alpha> \<and>
     ((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>g', \<sigma>ls')), toSeqState i (\<Sigma>g, \<Sigma>ls), toSeqState i (\<Sigma>g'1, \<Sigma>ls'1))
     \<in> (Seq_rel i (Guas\<^sub>c ! i), (Seq_rel i (Guas\<^sub>s ! i))\<^sup>*)\<^sub>Seq_rel i \<alpha> \<and>
     (\<Gamma>\<^sub>c,(c', toSeqState i (\<sigma>g', \<sigma>ls')),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
     \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
     (\<Gamma>\<^sub>s,(c\<^sub>s', toSeqState i (\<Sigma>g'1, \<Sigma>ls'1)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" 
       using alpha_rel_guar eq_\<Sigma>_par eq_toseq\<Sigma>' eq_toseq\<sigma>' by auto
    have "((\<sigma>g', \<sigma>ls'), (toPar i (\<Sigma>g', \<Sigma>ls') (\<Sigma>g, \<Sigma>ls))) \<in> \<alpha>"
    proof-                   
      have "(toSeqState i (\<sigma>g', (\<sigma>ls')), toSeqState i (toPar i (\<Sigma>g', \<Sigma>ls') (\<Sigma>g, \<Sigma>ls))) 
         \<in> Seq_rel i \<alpha>"
        using alpha_rel_guar eq_toseq\<sigma>' eq_toseq\<Sigma>'
        by fastforce     
      moreover have "R_wf (length (snd (toPar i (\<Sigma>g', \<Sigma>ls') (\<Sigma>g, \<Sigma>ls)))) \<alpha>"
      proof-
        have "length (snd (toPar i (\<Sigma>g', \<Sigma>ls') (\<Sigma>g, \<Sigma>ls))) = length \<Sigma>ls"
          by auto
        also have "R_wf (length \<Sigma>ls) \<alpha>"
          using a01 a02 a15 by auto
        finally show ?thesis by auto
      qed
      ultimately show ?thesis using Seq_rel_par
        using R_wf_def a02 alpha i_len local.step by fastforce
    qed
    then have "((\<sigma>g', \<sigma>ls'), \<Sigma>g'1,\<Sigma>ls'1) \<in> \<alpha>" using eq_\<Sigma>_par by auto
    moreover have step_par_s:
      "\<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (Coms\<^sub>s', (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sup>+ (Coms\<^sub>s'[i:=c\<^sub>s'], toPar i (\<Sigma>g', \<Sigma>ls') (\<Sigma>g, \<Sigma>ls))" 
      using mult_step_in_par1 a0' a01 a01'' a02 alpha_rel_guar a0'' step
    proof- 
       have f3:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (Coms\<^sub>s' ! i, toSeqPar i (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sup>+ (c\<^sub>s', (\<Sigma>g', \<Sigma>ls'))" 
        using alpha_rel_guar  
        apply (auto simp add: toSeqPar_toSeq_SeqState) apply (auto simp add: toSeq_def)
        by blast 
      then show ?thesis using mult_step_in_par_ev1[OF _ _ f3] 
         mult_step_in_par1 a0' a01 a01'' a02  a0'' step by auto      
    qed
    then have "\<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>v (Coms\<^sub>s', (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sup>+ (Coms\<^sub>s'[i:=c\<^sub>s'], \<Sigma>g'1,\<Sigma>ls'1)" using eq_\<Sigma>_par by auto
    then have "\<exists>a ab b.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                (\<exists>ac ad bb.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>(Some v) (a, ab, b) \<rightarrow> (ac, ad, bb) \<and> 
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>p (ac, ad, bb) \<rightarrow>\<^sub>\<tau>\<^sup>* (Coms\<^sub>s'[i:=c\<^sub>s'], (\<Sigma>g'1,\<Sigma>ls'1)))"
      by auto
    moreover have gcs:"(((\<sigma>g,\<sigma>ls), (\<sigma>g',\<sigma>ls')), (\<Sigma>g, \<Sigma>ls), 
                        toPar i (\<Sigma>g', \<Sigma>ls') (\<Sigma>g, \<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
    proof-
      have i_len:"i<length \<sigma>ls" 
        using a02 i_len step by auto
      moreover have "(((\<sigma>g, \<sigma>ls), \<sigma>g', \<sigma>ls'), (\<Sigma>g, \<Sigma>ls), fst (toPar i (\<Sigma>g', \<Sigma>ls') (\<Sigma>g, \<Sigma>ls)), 
                    snd (toPar i (\<Sigma>g', \<Sigma>ls') (\<Sigma>g, \<Sigma>ls))) \<in> (Guas\<^sub>c ! i, (Guas\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha>"
      proof-        
        have eq_len:"
          length \<sigma>ls' = length \<sigma>ls \<and> length \<sigma>ls = length \<Sigma>ls \<and>
          length \<Sigma>ls =  length (snd (toPar i (\<Sigma>g', \<Sigma>ls') (\<Sigma>g, \<Sigma>ls)))"
          using step a01 by auto        
         moreover have RF:"R_wf (length \<sigma>ls) (Guas\<^sub>c ! i) \<and> R_wf (length \<sigma>ls) (Guas\<^sub>s ! i)"
           using a16 a17   unfolding R_wf_def apply auto
           by (metis (no_types, hide_lams) UN_subset_iff  lessThan_iff 
                  subsetD  a0'  a0'' a02  a01'' a2 a1 step)+  
         ultimately show ?thesis using eq_toseq\<Sigma>' eq_toseq\<sigma>'
           by (metis  i_len  a02 a15 alpha_rel_guar prod.exhaust_sel rel_tran_seq)
       qed     
       moreover have "Guas\<^sub>c ! i \<subseteq> G\<^sub>c"
         by (metis (no_types) UN_subset_iff i_len a0' a02 a1 lessThan_iff)
       moreover have "Guas\<^sub>s ! i \<subseteq> G\<^sub>s"
         by (metis (no_types) UN_subset_iff i_len a0' a02 a2 lessThan_iff)
       ultimately show ?thesis by (simp add: G_comp1)       
     qed
     then have "(((\<sigma>g,\<sigma>ls), (\<sigma>g',\<sigma>ls')), (\<Sigma>g, \<Sigma>ls), \<Sigma>g'1, \<Sigma>ls'1) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
       using eq_\<Sigma>_par by auto
     moreover have 
       "(\<forall>i'<length PostsQ. (\<Gamma>\<^sub>c,(c\<^sub>c' ! i', toSeqState i' (\<sigma>g',\<sigma>ls')),
             Seq_rel i' (Rels\<^sub>c ! i'),Seq_rel i' (Guas\<^sub>c ! i')) 
          \<succeq>\<^sub>(\<^sub>Seq_rel i' \<alpha>\<^sub>;\<^sub>xx i' PostsQ\<^sub>;\<^sub>xx i' PostsA\<^sub>)
        (\<Gamma>\<^sub>s,(Coms\<^sub>s'[i:=c\<^sub>s'] ! i', toSeqState i' (\<Sigma>g'1, \<Sigma>ls'1)),
            Seq_rel i' (Rels\<^sub>s ! i'),Seq_rel i' (Guas\<^sub>s ! i')))"  
     proof-
       have aa:"i < length Coms\<^sub>c' \<and> (\<forall>j. j \<noteq> i \<longrightarrow> c\<^sub>c' ! j = Coms\<^sub>c' ! j) \<and> c\<^sub>c' ! i = c'" using step
         by blast    
       have "length \<sigma>ls = length PostsQ" and "length \<sigma>ls = length \<sigma>ls'" and 
              "length \<Sigma>ls = length \<sigma>ls" and len_\<Sigma>':"length \<Sigma>ls = length \<Sigma>ls'1"
         using eq_\<Sigma>_par by (auto simp add: a02 step a01 )       
       then show ?thesis 
         using rest_sim[OF a0 a0' a0''' a5' a0'' a01'' i_len 
               alpha_rel_guar' aa a15 a16 a17 a18 a19 a20 a21] by auto                 
     qed   
     then have "(\<forall>i'<length \<sigma>ls. (\<Gamma>\<^sub>c,(c\<^sub>c' ! i', toSeqState i' (\<sigma>g',\<sigma>ls')),
             Seq_rel i' (Rels\<^sub>c ! i'),Seq_rel i' (Guas\<^sub>c ! i')) 
          \<succeq>\<^sub>(\<^sub>Seq_rel i' \<alpha>\<^sub>;\<^sub>xx i' PostsQ\<^sub>;\<^sub>xx i' PostsA\<^sub>)
        (\<Gamma>\<^sub>s,(Coms\<^sub>s'[i:=c\<^sub>s'] ! i', toSeqState i' (\<Sigma>g'1, \<Sigma>ls'1)),
            Seq_rel i' (Rels\<^sub>s ! i'),Seq_rel i' (Guas\<^sub>s ! i')))"  
       using a15 unfolding R_wf_def
       by (metis (no_types, hide_lams) calculation(1)  local.step )                      
     moreover have "length Coms\<^sub>s' = length (Coms\<^sub>s'[i:=c\<^sub>s']) \<and>
                    length Coms\<^sub>s' = length c\<^sub>c' \<and> length \<sigma>ls = length \<sigma>ls' \<and> 
                    length \<sigma>ls = length  \<Sigma>ls'1"
       by (metis (no_types, hide_lams) R_wf_def a0'' a15 b01 
           calculation(1) length_list_update local.step step_pev_pair_elim_cases)
     ultimately have "(\<exists>c\<^sub>s' aa ba.
                (\<exists>a ab b.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                    (\<exists>ac ad bb.
                        \<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>Some v (a, ab, b) \<rightarrow> (ac, ad, bb) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>p (ac, ad, bb) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', aa, ba))) \<and>
                ((\<sigma>g',\<sigma>ls'), aa, ba) \<in> \<alpha> \<and>
                (((\<sigma>g, \<sigma>ls), \<sigma>g', \<sigma>ls'), (\<Sigma>g, \<Sigma>ls), aa, ba) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                ((\<forall>i<length \<sigma>ls. (\<Gamma>\<^sub>c,(c\<^sub>c' ! i, toSeqState i (\<sigma>g', \<sigma>ls')),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                     \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
                     (\<Gamma>\<^sub>s,(c\<^sub>s' ! i, toSeqState i (aa, ba)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))) \<and>
                 length Coms\<^sub>s' = length c\<^sub>s' \<and>
                 length Coms\<^sub>s' = length c\<^sub>c' \<and> length \<sigma>ls = length \<sigma>ls' \<and> length \<sigma>ls = length ba \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', \<sigma>g',\<sigma>ls'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', aa, ba),R\<^sub>s,G\<^sub>s)))" by blast
   }  
  moreover 
  { fix \<sigma>g' \<sigma>ls'  \<Sigma>g' \<Sigma>ls'
    assume b01:"(((\<sigma>g, \<sigma>ls), \<sigma>g', \<sigma>ls'), (\<Sigma>g, \<Sigma>ls), \<Sigma>g', \<Sigma>ls') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>"
    have len_sigma:"length \<sigma>ls = length \<sigma>ls'" 
      using R_wf_Rc b01 unfolding related_transitions_def R_wf_def by fastforce       
    moreover have len_Sigma:"length \<Sigma>ls = length \<Sigma>ls'" 
      using b01 a15 mem_Collect_eq unfolding related_transitions_def R_wf_def
      apply auto
      by metis
    moreover have len_sigma_Sigma:"length \<sigma>ls = length \<Sigma>ls" 
      using alpha a0' a15 unfolding R_wf_def by auto
    moreover have len_sigma_Sigma':"length \<sigma>ls = length \<Sigma>ls'" using len_Sigma calculation by auto
    moreover have "(\<forall>i<length \<sigma>ls. (\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i, toSeqState i (\<sigma>g', \<sigma>ls')),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
                (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i, toSeqState i (\<Sigma>g', \<Sigma>ls')),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i)))"    
    proof -
    { fix i
      assume i:"i<length \<sigma>ls"      
      then have i':"i<length PostsQ"
        by (simp add: a02)
      then have rels:"R\<^sub>c \<subseteq> Rels\<^sub>c ! i \<and> R\<^sub>s \<subseteq> Rels\<^sub>s ! i" using a0' a0 by auto
      then have sim:"(\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
                (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i, toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" 
        using a5 i by auto
      have rel:"(((\<sigma>g, \<sigma>ls), \<sigma>g', \<sigma>ls'), (\<Sigma>g, \<Sigma>ls), \<Sigma>g', \<Sigma>ls') \<in> (Rels\<^sub>c ! i, (Rels\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha> " 
        using G_comp1[OF _ _ _] b01 rels by auto        
      have "((toSeqState i (\<sigma>g, \<sigma>ls), toSeqState i (\<sigma>g', \<sigma>ls')), 
                   toSeqState i ((\<Sigma>g, \<Sigma>ls)), toSeqState i (\<Sigma>g', \<Sigma>ls')) \<in> 
                    (Seq_rel i (Rels\<^sub>c ! i), (Seq_rel i (Rels\<^sub>s ! i))\<^sup>*)\<^sub>(Seq_rel i \<alpha>)"
      proof- 
        have "R_wf (length \<sigma>ls) (Rels\<^sub>c ! i)" using a21
          by (simp add: a02 i)
        moreover have "R_wf (length \<sigma>ls) (Rels\<^sub>s ! i)" using a20
          by (simp add: a02 i)
        ultimately show ?thesis 
          using rel_tran_par[OF rel i _ _ _  len_sigma[THEN sym]] 
            len_sigma_Sigma len_sigma_Sigma a0'
          using a02 a15 len_sigma_Sigma' by auto             
        qed
      moreover obtain a1 a2 a3 b1 b2 b3 where 
        seq1:"toSeqState i (\<sigma>g', \<sigma>ls') = ((a1, a2), a3)" and 
        seq2:"toSeqState i (\<Sigma>g', \<Sigma>ls') = ((b1,b2), b3)"
          unfolding toSeqState_def
          by auto
      ultimately have "(\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i,((a1, a2), a3)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
              \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
              (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i, ((b1, b2), b3)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))"
        apply auto
        by (rule dest_sim_env_step[OF sim], assumption)      
      then have "(\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i,toSeqState i (\<sigma>g', \<sigma>ls')),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
              \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
              (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i, toSeqState i (\<Sigma>g', \<Sigma>ls')),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))"  
        using seq1 seq2 by auto     
    } then show ?thesis by auto qed    
    ultimately have 
      "(\<forall>i<length \<sigma>ls. (\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i, toSeqState i (\<sigma>g', \<sigma>ls')),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
                (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i, toSeqState i (\<Sigma>g', \<Sigma>ls')),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))) \<and>
            length \<sigma>ls = length \<sigma>ls' \<and> length \<sigma>ls = length \<Sigma>ls' \<or>
            (\<Gamma>\<^sub>c,(Coms\<^sub>c', \<sigma>g', \<sigma>ls'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Coms\<^sub>s', \<Sigma>g', \<Sigma>ls'),R\<^sub>s,G\<^sub>s)"
    by auto   
  }
  moreover 
  { 
    assume i:"(\<forall>i<length Coms\<^sub>s'. Coms\<^sub>c' ! i = LanguageCon.com.Skip)" and
           c_not_empty: "Coms\<^sub>c' \<noteq> []"
    have  sim:"\<forall>i<length Coms\<^sub>s'. 
           (\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
              \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>) 
           (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i, toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" 
      using a5 a0' a0'' a01 a01'' a02 by auto
    have "\<exists>ab bb. (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
               (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> 
                   ((\<Union>j<length PostsQ. (Guas\<^sub>c !j)), (\<Union>j<length PostsQ. (Guas\<^sub>s ! j))\<^sup>*)\<^sub>\<alpha> \<and>
                 ((\<sigma>g, \<sigma>ls), ab, bb) \<in> (\<Inter>i<length PostsQ.  (PostsQ ! i)) \<and> \<gamma>\<^sub>n \<subseteq> \<alpha> \<and>
              (\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', ab, bb) \<and>
                    (\<forall>i<length c\<^sub>s'. c\<^sub>s' ! i = LanguageCon.com.Skip) \<and> c\<^sub>s' \<noteq> [])"      
      apply (rule sim_final_skip[of Rels\<^sub>c Guas\<^sub>c Guas\<^sub>s Rels\<^sub>s PostsA PostsQ Coms\<^sub>s' Coms\<^sub>c' 
                                   R\<^sub>c R\<^sub>s G\<^sub>c G\<^sub>s ])     
      using a0 a1 a2 a15 a16 alpha  a17 a20 a21 i a10 a11 
            c_not_empty a0' a0''' a0''  a5 a01 a01'' a02
               apply (auto intro: R_wf_to_Rel_fwf)[19]                              
      using a22 a0' a0''' R_wf_to_Rel_fwf Rel_wf_mon      
       apply (metis (no_types, hide_lams) Rel_wf_mon lessE nat_less_le) 
      using a9 by auto
    then have "\<exists>ab bb. (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                ((\<sigma>g, \<sigma>ls), ab, bb) \<in> \<gamma>\<^sub>n \<and> \<gamma>\<^sub>n \<subseteq> \<alpha> \<and>
                (\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', ab, bb) \<and>
                (\<forall>i<length c\<^sub>s'. c\<^sub>s' ! i = LanguageCon.com.Skip) \<and> c\<^sub>s' \<noteq> [])"      
      using a3 by auto
  }
  moreover 
  { 
    assume i:"throw_program Coms\<^sub>c'" 
    have  sim:"\<forall>i<length Coms\<^sub>s'. 
           (\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
              \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>) 
           (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i, toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" 
      using a5 a0' a0'' a01 a01'' a02 by auto
    have "\<exists>ab bb. (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
               (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> 
                   ((\<Union>j<length PostsQ. (Guas\<^sub>c !j)), (\<Union>j<length PostsQ. (Guas\<^sub>s ! j))\<^sup>*)\<^sub>\<alpha> \<and>
                 ((\<sigma>g, \<sigma>ls), ab, bb) \<in> (\<Union>i<length PostsA.  (PostsA ! i)) \<and> \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
              (\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', ab, bb) \<and> throw_program c\<^sub>s')"          
      apply (rule sim_final_throw[of Rels\<^sub>c Guas\<^sub>c Guas\<^sub>s Rels\<^sub>s PostsA PostsQ Coms\<^sub>s' Coms\<^sub>c' 
                                   R\<^sub>c R\<^sub>s G\<^sub>c G\<^sub>s ])     
      using a0 a1 a2 a15 a16 alpha  a17 a20 a21 i a10 a11 
             a0' a0''' a0''  a5 a01 a01'' a02
               apply (auto intro: R_wf_to_Rel_fwf)[19]                              
      using  a23 a0' a0''' R_wf_to_Rel_fwf Rel_wf_mon      
         apply (metis (no_types, hide_lams) Rel_wf_mon lessE nat_less_le) 
      using  a22 a0' a0''' R_wf_to_Rel_fwf Rel_wf_mon      
        apply (metis (no_types, hide_lams) Rel_wf_mon lessE nat_less_le)      
      using a9 a8 a0' by auto
    then have "\<exists>ab bb.
              (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
              ((\<sigma>g, \<sigma>ls), ab, bb) \<in> \<gamma>\<^sub>a \<and> \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
              (\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', ab, bb) \<and> throw_program c\<^sub>s')"
      using a4 by auto
  }
  moreover 
  { 
    assume i:"final_error Coms\<^sub>c'" 
    have  sim:"\<forall>i<length Coms\<^sub>s'. 
           (\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i, toSeqState i (\<sigma>g, \<sigma>ls)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
              \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>) 
           (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i, toSeqState i (\<Sigma>g, \<Sigma>ls)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))" 
      using a5 a0' a0'' a01 a01'' a02 by auto
    have "\<exists>ab bb. (((\<sigma>g, \<sigma>ls), (\<sigma>g, \<sigma>ls)), (\<Sigma>g, \<Sigma>ls), ab, bb) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>              
              (\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', (\<Sigma>g, \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', ab, bb) \<and> final_error_r Coms\<^sub>c' c\<^sub>s')"
      apply (rule sim_final_error[of Rels\<^sub>c Guas\<^sub>c Guas\<^sub>s Rels\<^sub>s PostsA PostsQ Coms\<^sub>s' Coms\<^sub>c'  R\<^sub>c R\<^sub>s G\<^sub>c G\<^sub>s ])
       using a0 a1 a2 a15 a16 alpha  a17 a20 a21 i a10 a11 a0' a0''' a0''  a5 a01 a01'' a02
                           apply (auto intro: R_wf_to_Rel_fwf)[19]
       using  a23 a0' a0''' R_wf_to_Rel_fwf Rel_wf_mon      
          apply (metis (no_types, hide_lams) Rel_wf_mon lessE nat_less_le) 
      using  a22 a0' a0''' R_wf_to_Rel_fwf Rel_wf_mon      
        apply (metis (no_types, hide_lams) Rel_wf_mon lessE nat_less_le)      
      using a9 a8 a0' by auto      
  }
  ultimately show "((\<sigma>g, \<sigma>ls), \<Sigma>g, \<Sigma>ls) \<in> \<alpha> \<and>
        (\<forall>c\<^sub>c' a b.
            (\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>\<tau> (Coms\<^sub>c', \<sigma>g, \<sigma>ls) \<rightarrow> (c\<^sub>c', a, b)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', aa, ba) \<and>
                ((a, b), aa, ba) \<in> \<alpha> \<and>
                (((\<sigma>g, \<sigma>ls), a, b), (\<Sigma>g, \<Sigma>ls), aa, ba) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                ((\<forall>i<length \<sigma>ls.
                     (\<Gamma>\<^sub>c,(c\<^sub>c' ! i,
                            toSeqState i (a, b)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                     \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
                     (\<Gamma>\<^sub>s,(c\<^sub>s' ! i,
                            toSeqState i
                             (aa, ba)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))) \<and>
                 length Coms\<^sub>s' = length c\<^sub>s' \<and>
                 length Coms\<^sub>s' = length c\<^sub>c' \<and>
                 length \<sigma>ls = length b \<and> length \<sigma>ls = length ba \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', a, b),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', aa, ba),R\<^sub>s,G\<^sub>s)))) \<and>
        (\<forall>v c\<^sub>c' a b.
            (\<Gamma>\<^sub>c\<turnstile>\<^sub>p\<^sub>(Some v) (Coms\<^sub>c', \<sigma>g, \<sigma>ls) \<rightarrow> (c\<^sub>c', a, b)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                (\<exists>a ab b.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                    (\<exists>ac ad bb.
                        (\<Gamma>\<^sub>s\<turnstile>\<^sub>p\<^sub>(Some v) (a, ab, b) \<rightarrow> (ac, ad, bb)) \<and>
                        \<Gamma>\<^sub>s\<turnstile>\<^sub>p (ac, ad, bb) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', aa, ba))) \<and>
                ((a, b), aa, ba) \<in> \<alpha> \<and>
                (((\<sigma>g, \<sigma>ls), a, b), (\<Sigma>g, \<Sigma>ls), aa, ba) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                ((\<forall>i<length \<sigma>ls.
                     (\<Gamma>\<^sub>c,(c\<^sub>c' ! i,
                            toSeqState i (a, b)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                     \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
                     (\<Gamma>\<^sub>s,(c\<^sub>s' ! i,
                            toSeqState i
                             (aa, ba)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))) \<and>
                 length Coms\<^sub>s' = length c\<^sub>s' \<and>
                 length Coms\<^sub>s' = length c\<^sub>c' \<and>
                 length \<sigma>ls = length b \<and> length \<sigma>ls = length ba \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', a, b),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                 (\<Gamma>\<^sub>s,(c\<^sub>s', aa, ba),R\<^sub>s,G\<^sub>s)))) \<and>
        (\<forall>a b aa ba.
            (((\<sigma>g, \<sigma>ls), a, b), (\<Sigma>g, \<Sigma>ls), aa, ba) \<in> ((R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<longrightarrow>
            (\<forall>i<length \<sigma>ls.
                (\<Gamma>\<^sub>c,(Coms\<^sub>c' ! i,
                       toSeqState i (a, b)),Seq_rel i (Rels\<^sub>c ! i),Seq_rel i (Guas\<^sub>c ! i))
                \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i PostsQ\<^sub>;\<^sub>xx i PostsA\<^sub>)
                (\<Gamma>\<^sub>s,(Coms\<^sub>s' ! i,
                       toSeqState i (aa, ba)),Seq_rel i (Rels\<^sub>s ! i),Seq_rel i (Guas\<^sub>s ! i))) \<and>
            length \<sigma>ls = length b \<and> length \<sigma>ls = length ba \<or>
            (\<Gamma>\<^sub>c,(Coms\<^sub>c', a, b),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
            (\<Gamma>\<^sub>s,(Coms\<^sub>s', aa, ba),R\<^sub>s,G\<^sub>s)) \<and>
        ((\<forall>i<length Coms\<^sub>s'. Coms\<^sub>c' ! i = LanguageCon.com.Skip) \<and> Coms\<^sub>c' \<noteq> [] \<longrightarrow>
         (\<exists>a b. (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), a, b) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                ((\<sigma>g, \<sigma>ls), a, b) \<in> \<gamma>\<^sub>n \<and>
                \<gamma>\<^sub>n \<subseteq> \<alpha> \<and>
                (\<exists>c\<^sub>s'.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', a, b) \<and>
                    (\<forall>i<length c\<^sub>s'. c\<^sub>s' ! i = LanguageCon.com.Skip) \<and> c\<^sub>s' \<noteq> []))) \<and>
        (throw_program Coms\<^sub>c' \<longrightarrow>
         (\<exists>a b. (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), a, b) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                ((\<sigma>g, \<sigma>ls), a, b) \<in> \<gamma>\<^sub>a \<and>
                \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
                (\<exists>c\<^sub>s'.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', a, b) \<and> throw_program c\<^sub>s'))) \<and>
        (final_error Coms\<^sub>c' \<longrightarrow>
         (\<exists>a b. (((\<sigma>g, \<sigma>ls), \<sigma>g, \<sigma>ls), (\<Sigma>g, \<Sigma>ls), a, b) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                (\<exists>c\<^sub>s'. \<Gamma>\<^sub>s\<turnstile>\<^sub>p (Coms\<^sub>s', \<Sigma>g, \<Sigma>ls) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', a, b) \<and> final_error_r Coms\<^sub>c' c\<^sub>s')))" 
    by auto
   
qed
  
lemma sim_comp_sound:
  assumes a0':"length C>0" and
 a0:"\<forall>i<length C.
       R\<^sub>c \<union> (\<Union>j\<in>{j. j < length C \<and> j \<noteq> i}. (Gua\<^sub>c (C ! j)))
       \<subseteq> (Rel\<^sub>c (C ! i)) \<and>
       R\<^sub>s \<union> (\<Union>j\<in>{j. j < length C \<and> j \<noteq> i}. (Gua\<^sub>s (C ! j)))
       \<subseteq> (Rel\<^sub>s (C ! i))" and
 a1:" (\<Union>j<length C. (Gua\<^sub>c (C ! j))) \<subseteq> G\<^sub>c" and 
 a2:" (\<Union>j<length C. (Gua\<^sub>s (C ! j))) \<subseteq> G\<^sub>s" and             
 a3:" (\<Inter>i<length C.  (PostQ (C ! i))) \<subseteq> \<gamma>\<^sub>n" and 
 a4:" (\<Union>i<length C.  (PostA (C ! i))) \<subseteq> \<gamma>\<^sub>a " and 
 a5:" \<forall>i<length C.                                                    
      \<forall>\<gamma>\<^sub>n \<gamma>\<^sub>a. \<gamma>\<^sub>n = Seq_rel i (PostQ (C !i)) \<and> \<gamma>\<^sub>a = Seq_rel i (PostA (C!i)) \<longrightarrow>
     (\<Gamma>\<^sub>c, (Com\<^sub>c (C! i),toSeqState i \<sigma>),Seq_rel i (Rel\<^sub>c (C!i)), Seq_rel i (Gua\<^sub>c (C!i)))
       \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) 
     (\<Gamma>\<^sub>s,(Com\<^sub>s (C! i),toSeqState i s\<^sub>s),Seq_rel i (Rel\<^sub>s (C!i)), Seq_rel i (Gua\<^sub>s (C!i)))" and  
 a8:"\<forall>i<length C.
       Sta\<^sub>s (PostA (C ! i)) (Rel\<^sub>c (C ! i), (Rel\<^sub>s (C ! i))\<^sup>*)\<^sub>\<alpha>" and
 a9:"\<forall>i<length C.
       Sta\<^sub>s (PostQ (C ! i)) (Rel\<^sub>c (C ! i), (Rel\<^sub>s (C ! i))\<^sup>*)\<^sub>\<alpha>" and  
 a10:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a11:"\<gamma>\<^sub>a \<subseteq> \<alpha>"  and 
 a12:"\<forall>i<length C. \<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>)\<in> ((Gua\<^sub>c (C ! i)))" and
 a13:"length C = length (snd \<sigma>)" and a14:"length C = length (snd s\<^sub>s)" and 
 a15:"R_wf (length C) \<alpha>" and a16:"R_wf (length C) G\<^sub>c" and a17:"R_wf (length C) G\<^sub>s" and
 a20:"\<forall>i<length C. R_wf (length C) (Rel\<^sub>s (C!i))" and
 a21:"\<forall>i<length C. R_wf (length C) (Rel\<^sub>c (C!i))" and 
 a22:"\<forall>i<length C. R_wf (length C) (PostQ (C!i))" and
 a23:"\<forall>i<length C. R_wf (length C) (PostA (C!i))"

shows "(\<Gamma>\<^sub>c,(PCom\<^sub>c C,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(PCom\<^sub>s C,s\<^sub>s),R\<^sub>s,G\<^sub>s)"
proof-
  let ?Rels\<^sub>c = "par_sim_list Rel\<^sub>c C" and
      ?Rels\<^sub>s = "par_sim_list Rel\<^sub>s C" and
      ?Guas\<^sub>c = "par_sim_list Gua\<^sub>c C" and
      ?Guas\<^sub>s = "par_sim_list Gua\<^sub>s C" and
      ?PostsQ = "par_sim_list PostQ C" and
      ?PostsA = "par_sim_list PostA C" and
      ?Coms\<^sub>c = "par_sim_list Com\<^sub>c C" and
      ?Coms\<^sub>s = "par_sim_list Com\<^sub>s C"
      
  have a0'': "length ?Rels\<^sub>c = length ?Guas\<^sub>c \<and> length ?Rels\<^sub>c = length ?PostsQ \<and> length ?Rels\<^sub>c = length ?PostsA \<and>
         length ?Rels\<^sub>c = length ?Guas\<^sub>s \<and> length ?Rels\<^sub>c = length ?Rels\<^sub>s" unfolding par_sim_list_def by auto
  have a01'':"length ?Rels\<^sub>c = length ?Coms\<^sub>s \<and> length ?Rels\<^sub>c = length ?Coms\<^sub>c"  unfolding par_sim_list_def by auto
  have a0''':"length ?Rels\<^sub>c>0" using a0' unfolding par_sim_list_def by auto
  have a0':"\<forall>i<length ?Rels\<^sub>c.
       R\<^sub>c \<union> (\<Union>j\<in>{j. j < length ?Guas\<^sub>c \<and> j \<noteq> i}. (?Guas\<^sub>c ! j))
       \<subseteq> (?Rels\<^sub>c ! i) \<and>
       R\<^sub>s \<union> (\<Union>j\<in>{j. j < length ?Guas\<^sub>s \<and> j \<noteq> i}. (?Guas\<^sub>s ! j))
       \<subseteq> (?Rels\<^sub>s!i)" using a0 unfolding par_sim_list_def Gua\<^sub>c_def Rel\<^sub>c_def by auto  
  have a1':"(\<Union>j<length ?Guas\<^sub>c. (?Guas\<^sub>c !j)) \<subseteq> G\<^sub>c" 
    using a1 unfolding par_sim_list_def Gua\<^sub>c_def  by auto
  have a2':" (\<Union>j<length ?Guas\<^sub>s. (?Guas\<^sub>s ! j)) \<subseteq> G\<^sub>s"      
     using a2 unfolding par_sim_list_def Gua\<^sub>s_def  by auto
  have a3':" (\<Inter>i<length ?PostsQ.  (?PostsQ ! i)) \<subseteq> \<gamma>\<^sub>n" 
     using a3 unfolding par_sim_list_def PostQ_def by auto
  have a4':" (\<Union>i<length ?PostsA.  (?PostsA ! i)) \<subseteq> \<gamma>\<^sub>a " 
    using a4 unfolding par_sim_list_def PostA_def by auto  
  have a5':" \<forall>i<length ?PostsQ.                                                          
     (\<Gamma>\<^sub>c, (?Coms\<^sub>c ! i,toSeqState i \<sigma>),Seq_rel i (?Rels\<^sub>c !i), Seq_rel i (?Guas\<^sub>c!i)) 
        \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>xx i ?PostsQ\<^sub>;\<^sub>xx i ?PostsA\<^sub>) 
     (\<Gamma>\<^sub>s,(?Coms\<^sub>s! i,toSeqState i s\<^sub>s),Seq_rel i (?Rels\<^sub>s!i), Seq_rel i (?Guas\<^sub>s !i))"
    using a5 unfolding par_sim_list_def xx_def by auto
  have a8':"\<forall>i<length ?PostsA.
     Sta\<^sub>s (?PostsA ! i) ((?Rels\<^sub>c ! i), (?Rels\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha>" 
    using a8  unfolding par_sim_list_def by auto
  have a9':"\<forall>i<length ?PostsQ.
     Sta\<^sub>s (?PostsQ ! i) ((?Rels\<^sub>c ! i), (?Rels\<^sub>s ! i)\<^sup>*)\<^sub>\<alpha>" 
    using a9  unfolding par_sim_list_def by auto
  have a12': "\<forall>i<length ?PostsQ. \<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>)\<in> ((?Guas\<^sub>c ! i))" 
    using a12 unfolding par_sim_list_def by auto
  have a13: "length ?PostsQ = length (snd \<sigma>)" using a13 unfolding par_sim_list_def by auto
  have a14: "length ?PostsQ = length (snd s\<^sub>s)" using a14 unfolding par_sim_list_def by auto  
  have a15:"R_wf (length ?PostsQ) \<alpha>" using a15 unfolding par_sim_list_def by auto
  have a16:"R_wf (length ?PostsQ) G\<^sub>c" using a16 unfolding par_sim_list_def by auto
  have a17:"R_wf (length ?PostsQ) G\<^sub>s" using a17 unfolding par_sim_list_def by auto
  have a18:"\<forall>i<length ?PostsQ. R_wf (length ?PostsQ) (?Rels\<^sub>s!i)" using a20 
    unfolding par_sim_list_def by auto
  have a19:"\<forall>i<length ?PostsQ. R_wf (length ?PostsQ) (?Rels\<^sub>c!i)" using a21 
    unfolding par_sim_list_def by auto
  have a22:"\<forall>i<length ?PostsQ. R_wf (length ?PostsQ) (?PostsQ!i)" using a22
    unfolding par_sim_list_def by auto
  have a23:"\<forall>i<length ?PostsQ. R_wf (length ?PostsQ) (?PostsA!i)" using a23
    unfolding par_sim_list_def by auto
  have "(\<Gamma>\<^sub>c,(?Coms\<^sub>c,\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(?Coms\<^sub>s,s\<^sub>s),R\<^sub>s,G\<^sub>s)" 
    using sim_comp_sound1[OF a0'' a01'' a0''' a0' a1' a2' a3' a4' a5' a8' a9' 
                             a10 a11 a12' a13 a14 a15 a16 a17 a18 a19 a22 a23]  
    
  by auto
thus ?thesis unfolding PCom\<^sub>c_def PCom\<^sub>s_def par_sim_list_def by auto
qed
  
lemma subset_R_wf: assumes a0:"\<xi> \<subseteq> \<alpha>" and 
              a1:"R_wf (length C) \<alpha>" and a2: "(\<sigma>,\<Sigma>)\<in> \<xi>"
            shows  "length C = length (snd \<sigma>)"
  using a0 a1 a2 unfolding R_wf_def
  by (metis prod.exhaust_sel subsetD)


lemma subset_R_wf1: assumes a0:"0 < length C" and "\<xi> \<subseteq> (\<Inter>i<length C.  (Pre (C ! i)))" and
              a1:"\<forall>i<length C. R_wf (length C) (Pre (C!i))" and a2: "(\<sigma>,\<Sigma>)\<in> \<xi>"
            shows  "length C = length (snd \<sigma>)"
  using a0 a1 a2 unfolding R_wf_def
 proof -
  have "(\<sigma>, \<Sigma>) \<in> Sim_Rules.Pre (C ! 0)"
    using a0 a2 assms(2) by auto
  then show ?thesis
    by (meson a0 a1 order.order_iff_strict subset_R_wf)
qed


lemma subset_R_wf2: assumes a0:"0 < length C" and "\<xi> \<subseteq> (\<Inter>i<length C.  (Pre (C ! i)))" and
              a1:"\<forall>i<length C. R_wf (length C) (Pre (C!i))" and a2: "(\<sigma>,\<Sigma>)\<in> \<xi>"
            shows  "length C = length (snd \<Sigma>)"
  using a0 a1 a2 unfolding R_wf_def
 proof -
  have "(\<sigma>, \<Sigma>) \<in> Sim_Rules.Pre (C ! 0)"
    using a0 a2 assms(2) by auto
  then show ?thesis  by (metis (no_types, hide_lams) R_wf_def a0 a1 prod.exhaust_sel)    
qed

lemma in_seq_rel:"R_wf n \<xi>\<^sub>s \<Longrightarrow>
       ((\<sigma>g, \<sigma>l), \<Sigma>g, \<Sigma>l) \<in> \<xi> \<Longrightarrow> 
       \<xi> \<subseteq> \<xi>\<^sub>s \<Longrightarrow> i < n \<Longrightarrow>
       (toSeqState i  (\<sigma>g, \<sigma>l), toSeqState i (\<Sigma>g,\<Sigma>l)) \<in> Seq_rel i \<xi>\<^sub>s"
  apply (rule par_rel_seq_rel)
  apply blast
  by (metis (no_types) R_wf_def subsetD)+

lemma split_pre_sim: assumes  a0:"\<forall>i<length C.
         \<forall>\<xi> \<gamma>\<^sub>n \<gamma>\<^sub>a.
            \<xi> = Seq_rel i (Pre (C ! i)) \<and>
            \<gamma>\<^sub>n = Seq_rel i (PostQ (C ! i)) \<and> \<gamma>\<^sub>a = Seq_rel i (PostA (C ! i)) \<longrightarrow>
            (\<forall>\<sigma> \<Sigma>. (\<sigma>, \<Sigma>) \<in> \<xi> \<longrightarrow> (\<Gamma>\<^sub>c,(Com\<^sub>c (C ! i), \<sigma>),Seq_rel i (Rel\<^sub>c (C ! i)),Seq_rel i (Gua\<^sub>c (C ! i)))
                    \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                    (\<Gamma>\<^sub>s,(Com\<^sub>s (C ! i), \<Sigma>),Seq_rel i (Rel\<^sub>s (C ! i)),Seq_rel i (Gua\<^sub>s (C ! i))))" and
    a1:"\<forall>i<length C. R_wf (length C) (Pre (C!i)) " and a2:"\<xi> \<subseteq> (\<Inter>i<length C.  (Pre (C ! i)))" and 
    a3:"(\<sigma>,\<Sigma>)\<in>\<xi>" 
  shows "\<forall>i<length C.  \<forall>\<gamma>\<^sub>n \<gamma>\<^sub>a.
         \<gamma>\<^sub>n = Seq_rel i (PostQ (C ! i)) \<and> \<gamma>\<^sub>a = Seq_rel i (PostA (C ! i)) \<longrightarrow>
         (\<Gamma>\<^sub>c,(Com\<^sub>c (C ! i), toSeqState i \<sigma>),Seq_rel i (Rel\<^sub>c (C ! i)),Seq_rel i (Gua\<^sub>c (C ! i)))
         \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
         (\<Gamma>\<^sub>s,(Com\<^sub>s (C ! i), toSeqState i \<Sigma>),Seq_rel i (Rel\<^sub>s (C ! i)),Seq_rel i (Gua\<^sub>s (C ! i)))"
proof-
  {fix i
    let ?p = "(PostQ (C ! i))" let ?q = "(PostA (C ! i))"
    assume "i < length C"
    moreover obtain \<sigma>1 \<sigma>2 \<Sigma>1 \<Sigma>2 where aa:"\<sigma> = (\<sigma>1,\<sigma>2)" and bb:"\<Sigma> = (\<Sigma>1, \<Sigma>2)"
      by moura 
    moreover have "(toSeqState i  (\<sigma>1,\<sigma>2), toSeqState i (\<Sigma>1, \<Sigma>2)) \<in> Seq_rel i (Pre (C!i))"
      using a1 a2 a3 calculation
      by (blast intro: in_seq_rel[of "length C" "Pre (C!i)" \<sigma>1 \<sigma>2 \<Sigma>1 \<Sigma>2 \<xi> i])     
    ultimately have "(\<Gamma>\<^sub>c,(Com\<^sub>c (C ! i), toSeqState i \<sigma>),Seq_rel i (Rel\<^sub>c (C ! i)),Seq_rel i (Gua\<^sub>c (C ! i)))
         \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>Seq_rel i ?p\<^sub>;\<^sub>Seq_rel i ?q\<^sub>)
         (\<Gamma>\<^sub>s,(Com\<^sub>s (C ! i), toSeqState i \<Sigma>),Seq_rel i (Rel\<^sub>s (C ! i)),Seq_rel i (Gua\<^sub>s (C ! i)))" 
      using a0  by fast
          
  } thus ?thesis by auto
qed
 
lemma sim_comp:
  "length C > 0 \<Longrightarrow> 
   \<forall>i<length C.
       R\<^sub>c \<union> (\<Union>j\<in>{j. j < length C \<and> j \<noteq> i}. (Gua\<^sub>c (C ! j)))
       \<subseteq> (Rel\<^sub>c (C ! i)) \<and>
       R\<^sub>s \<union> (\<Union>j\<in>{j. j < length C \<and> j \<noteq> i}. (Gua\<^sub>s (C ! j)))
       \<subseteq> (Rel\<^sub>s (C ! i)) \<Longrightarrow>
    (\<Union>j<length C. (Gua\<^sub>c (C ! j))) \<subseteq> G\<^sub>c \<Longrightarrow>  
    (\<Union>j<length C. (Gua\<^sub>s (C ! j))) \<subseteq> G\<^sub>s \<Longrightarrow>   
     \<xi> \<subseteq> (\<Inter>i<length C.  (Pre (C ! i))) \<Longrightarrow>     
     (\<Inter>i<length C.  (PostQ (C ! i))) \<subseteq> \<gamma>\<^sub>n \<Longrightarrow>
     (\<Union>i<length C.  (PostA (C ! i))) \<subseteq> \<gamma>\<^sub>a \<Longrightarrow>
    \<forall>i<length C.
      \<forall>\<xi> \<gamma>\<^sub>n \<gamma>\<^sub>a. \<xi> = Seq_rel i  (Pre (C !i)) \<and> \<gamma>\<^sub>n = Seq_rel i (PostQ (C !i)) \<and> \<gamma>\<^sub>a = Seq_rel i (PostA (C!i)) \<longrightarrow>
     (\<Gamma>\<^sub>c, Com\<^sub>c (C! i),Seq_rel i (Rel\<^sub>c (C!i)), Seq_rel i (Gua\<^sub>c (C!i))) 
        \<succeq>\<^sub>(\<^sub>Seq_rel i \<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,Com\<^sub>s (C! i),Seq_rel i (Rel\<^sub>s (C!i)), Seq_rel i  (Gua\<^sub>s (C!i))) \<Longrightarrow>
    \<gamma>\<^sub>n \<subseteq> \<alpha> \<Longrightarrow> \<gamma>\<^sub>a \<subseteq> \<alpha> \<Longrightarrow>
   \<forall>i<length C.
       Sta\<^sub>s (PostA (C ! i)) (Rel\<^sub>c (C ! i), (Rel\<^sub>s (C ! i))\<^sup>*)\<^sub>\<alpha> \<Longrightarrow>
   \<forall>i<length C.
       Sta\<^sub>s (PostQ (C ! i)) (Rel\<^sub>c (C ! i), (Rel\<^sub>s (C ! i))\<^sup>*)\<^sub>\<alpha> \<Longrightarrow> 
   \<forall>i<length C. \<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>)\<in> ((Gua\<^sub>c (C ! i))) \<Longrightarrow> R_wf (length C) \<alpha> \<Longrightarrow> R_wf (length C) G\<^sub>c \<Longrightarrow>
   R_wf (length C) G\<^sub>s \<Longrightarrow> \<forall>i<length C. R_wf (length C) (Rel\<^sub>s (C!i)) \<Longrightarrow> \<forall>i<length C. R_wf (length C) (Pre (C!i)) \<Longrightarrow>
   \<forall>i<length C. R_wf (length C) (Rel\<^sub>c (C!i)) \<Longrightarrow>  
   \<forall>i<length C. R_wf (length C) (PostQ (C!i)) \<Longrightarrow> 
   \<forall>i<length C. R_wf (length C) (PostA (C!i)) \<Longrightarrow>
   (\<Gamma>\<^sub>c,PCom\<^sub>c C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>p\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,PCom\<^sub>s C,R\<^sub>s,G\<^sub>s)" 
 unfolding RGSIM_p_pre_def RGSim_pre_def Pre_def
  apply (rule, rule,rule) apply (rule sim_comp_sound) 
        apply fast apply fast apply fast apply fast
               apply fast apply fast apply (rule split_pre_sim[of C \<Gamma>\<^sub>c \<alpha> \<Gamma>\<^sub>s \<xi>, simplified Pre_def], assumption+)
         apply (rule subset_R_wf1[of C \<xi>, simplified Pre_def], assumption+)
  by (rule subset_R_wf2[of C \<xi>, simplified Pre_def], assumption+)  

lemma "\<alpha>' \<subseteq> \<alpha> \<Longrightarrow> \<alpha>\<subseteq> \<alpha>\<^sub>x \<Longrightarrow> \<alpha>' \<subseteq> \<alpha>\<^sub>x" by auto


lemma RGSim_Conseq_sound:
assumes  a0:"(\<Gamma>\<^sub>c,(C\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s)" and   
    a1:"\<gamma>\<^sub>n \<subseteq> \<gamma>\<^sub>n\<^sub>' \<and> \<gamma>\<^sub>n\<^sub>' \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>a \<subseteq> \<gamma>\<^sub>a\<^sub>' \<and> \<gamma>\<^sub>a\<^sub>' \<subseteq> \<alpha>" and 
   a3:"R\<^sub>s' \<subseteq> R\<^sub>s" and a4:"R\<^sub>c' \<subseteq> R\<^sub>c" and a5:"G\<^sub>s \<subseteq> G\<^sub>s'" and a6: "G\<^sub>c\<subseteq>G\<^sub>c'"  and a8:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>)\<in>G\<^sub>c"
 shows "(\<Gamma>\<^sub>c,(C\<^sub>c, \<sigma>),R\<^sub>c',G\<^sub>c') \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>'\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, \<Sigma>),R\<^sub>s',G\<^sub>s')"
  using a0
proof(coinduction arbitrary: C\<^sub>c C\<^sub>s \<sigma> \<Sigma>,clarsimp) 
  fix C\<^sub>c' C\<^sub>s' \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g  \<Sigma>l \<Sigma>ls 
  let ?\<sigma> = "((\<sigma>g::'b, \<sigma>l::'c), \<sigma>ls::'c list)"
  let ?\<Sigma> = "((\<Sigma>g::'f, \<Sigma>l::'g), \<Sigma>ls::'g list)"
  assume a0:"(\<Gamma>\<^sub>c,(C\<^sub>c', ((\<sigma>g, \<sigma>l), \<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
  have rg:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>)\<in>G\<^sub>c'" using a6 a8 by fast
  then have " (?\<sigma>, ?\<Sigma>) \<in> \<alpha>"
    using  a0 dest_sim_alpha by blast
  moreover {
    fix c\<^sub>c' \<sigma>g' \<sigma>l'
    let ?\<sigma>' = "((\<sigma>g'::'b, \<sigma>l'::'c), \<sigma>ls::'c list)"
    assume a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (C\<^sub>c', toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c',  toSeq ((\<sigma>g', \<sigma>l'), \<sigma>ls))"    
    then obtain c\<^sub>s' \<Sigma>g' \<Sigma>l' where step:"
       \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s',  toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<and>
       (?\<sigma>', ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<in> \<alpha> \<and>
       (((?\<sigma>, ?\<sigma>'), ?\<Sigma>, ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
       (\<Gamma>\<^sub>c,(c\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)),R\<^sub>s,G\<^sub>s)" 
      using dest_sim_tau_step[OF a0 a00] by auto
    let ?\<Sigma>' = "((\<Sigma>g'::'f, \<Sigma>l'::'g), \<Sigma>ls::'g list)"
    have "\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
           (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((\<Sigma>g', \<Sigma>l'),\<Sigma>ls))) \<and>
           (?\<sigma>', ((\<Sigma>g', \<Sigma>l'),\<Sigma>ls)) \<in> \<alpha> \<and>
           (((?\<sigma>, ?\<sigma>'), ?\<Sigma>, ((\<Sigma>g', \<Sigma>l'),\<Sigma>ls)) \<in> (G\<^sub>c', G\<^sub>s'\<^sup>*)\<^sub>\<alpha>) \<and>
           ((\<Gamma>\<^sub>c,(c\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',((\<Sigma>g', \<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s) \<or>
            (\<Gamma>\<^sub>c,(c\<^sub>c', ?\<sigma>'),R\<^sub>c',G\<^sub>c') \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>'\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', ((\<Sigma>g', \<Sigma>l'),\<Sigma>ls)),R\<^sub>s',G\<^sub>s'))" using a5 a6 step
      by (meson G_comp1)
  } 
  moreover {
    fix  v c\<^sub>c' \<sigma>g' \<sigma>l'
    let ?\<sigma>' = "((\<sigma>g'::'b, \<sigma>l'::'c), \<sigma>ls::'c list)" 
    assume a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C\<^sub>c', toSeq ?\<sigma>) \<rightarrow> (c\<^sub>c', toSeq ?\<sigma>')"
    then have "\<exists>c\<^sub>s' \<Sigma>'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (C\<^sub>s', toSeq ?\<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s', toSeq (\<Sigma>', \<Sigma>ls)) \<and> 
               (?\<sigma>', (\<Sigma>', \<Sigma>ls)) \<in> \<alpha> \<and>
               (((?\<sigma>, ?\<sigma>'),  ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (\<Gamma>\<^sub>c,(c\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (\<Sigma>', \<Sigma>ls)),R\<^sub>s,G\<^sub>s)" 
      using dest_sim_ev_step[OF a0 a00]  by auto          
    then have "\<exists>c\<^sub>s' \<Sigma>'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (C\<^sub>s', toSeq ?\<Sigma>) \<rightarrow>\<^sup>+ (c\<^sub>s', toSeq (\<Sigma>', \<Sigma>ls)) \<and> 
               (?\<sigma>', (\<Sigma>', \<Sigma>ls)) \<in> \<alpha> \<and>
               (((?\<sigma>, ?\<sigma>'),  ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> (G\<^sub>c', G\<^sub>s'\<^sup>*)\<^sub>\<alpha>) \<and>
               (\<Gamma>\<^sub>c,(c\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (\<Sigma>', \<Sigma>ls)),R\<^sub>s,G\<^sub>s)" 
        using a5 a6 by (meson G_comp1) 
    then have  "\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
               (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                      (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)))) \<and>
               (?\<sigma>', ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<in> \<alpha> \<and>
               (((?\<sigma>, ?\<sigma>'),  ?\<Sigma>, ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<in> (G\<^sub>c', G\<^sub>s'\<^sup>*)\<^sub>\<alpha>) \<and>
               ((\<Gamma>\<^sub>c,(c\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)),R\<^sub>s,G\<^sub>s) \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', ?\<sigma>'),R\<^sub>c',G\<^sub>c') \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>'\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)),R\<^sub>s',G\<^sub>s'))" 
      by fast      
  } 
  moreover{
    fix \<sigma>g' \<sigma>l' \<sigma>ls' \<Sigma>g' \<Sigma>l' \<Sigma>ls'
    let ?\<Sigma>' = "((\<Sigma>g'::'f, \<Sigma>l'::'g), \<Sigma>ls'::'g list)"
    let ?\<sigma>' = "((\<sigma>g'::'b, \<sigma>l'::'c), \<sigma>ls'::'c list)"
    assume a00:"(((?\<sigma>, ?\<sigma>'), ?\<Sigma>, ?\<Sigma>') \<in> (R\<^sub>c', R\<^sub>s'\<^sup>*)\<^sub>\<alpha>)"   
    then have a00:"((?\<sigma>, ?\<sigma>'), ?\<Sigma>, ?\<Sigma>') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> " 
      using a3 a4  by (meson G_comp1)    
    have "(\<Gamma>\<^sub>c,(C\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', ?\<Sigma>'),R\<^sub>s,G\<^sub>s) \<or> 
          (\<Gamma>\<^sub>c,(C\<^sub>c', ?\<sigma>'),R\<^sub>c',G\<^sub>c') \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>'\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', ?\<Sigma>'),R\<^sub>s',G\<^sub>s')" 
      using dest_sim_env_step[OF a0 a00] by auto    
    (* then have "(\<Gamma>\<^sub>c,(C\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', ?\<Sigma>'),R\<^sub>s,G\<^sub>s) \<or>
           (\<Gamma>\<^sub>c,(C\<^sub>c', ?\<sigma>'),R\<^sub>c',G\<^sub>c') \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>'\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', ?\<Sigma>'),R\<^sub>s',G\<^sub>s')"  by auto *)
  }note f4 = this
  moreover{       
    assume "C\<^sub>c' = Skip"
    then have a0:"(\<Gamma>\<^sub>c,(Skip,?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', ?\<Sigma>),R\<^sub>s,G\<^sub>s)"         
      using a0 by auto
    then have "\<exists>\<Sigma>'. ((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (?\<sigma>, (\<Sigma>', \<Sigma>ls)) \<in> \<gamma>\<^sub>n \<and> \<gamma>\<^sub>n \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeq (\<Sigma>',\<Sigma>ls))" 
      using sim_elim_cases_c(1)[OF a0] by fastforce
    then have   "\<exists>\<Sigma>'. (((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> (G\<^sub>c', G\<^sub>s'\<^sup>*)\<^sub>\<alpha>) \<and>
                     (?\<sigma>, (\<Sigma>',\<Sigma>ls)) \<in> \<gamma>\<^sub>n\<^sub>' \<and> \<gamma>\<^sub>n\<^sub>' \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeq (\<Sigma>',\<Sigma>ls))"
      by (meson G_comp1 a1 a5 a6 subsetD)  
  }
  moreover{   
    assume "C\<^sub>c' = Throw "
    then have a0:"(\<Gamma>\<^sub>c,(Throw,?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', ?\<Sigma>),R\<^sub>s,G\<^sub>s)"         
      using a0 by auto
    then have "\<exists>\<Sigma>'. ((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (?\<sigma>, (\<Sigma>', \<Sigma>ls)) \<in> \<gamma>\<^sub>a \<and> \<gamma>\<^sub>a \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, toSeq (\<Sigma>', \<Sigma>ls))"  
      using  sim_elim_cases_c(2)[OF a0] by fastforce
    then have "\<exists>\<Sigma>'. ((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> ((G\<^sub>c', G\<^sub>s'\<^sup>*)\<^sub>\<alpha>) \<and>
                     (?\<sigma>, (\<Sigma>', \<Sigma>ls)) \<in> \<gamma>\<^sub>a\<^sub>' \<and>
                     \<gamma>\<^sub>a\<^sub>' \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, toSeq (\<Sigma>', \<Sigma>ls))"
      by (meson G_comp1 a2 a5 a6 subsetD)    
  }
  moreover{   
    fix f
    assume "C\<^sub>c' = Fault f"
    then have a0:"(\<Gamma>\<^sub>c,(Fault f,?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', ?\<Sigma>),R\<^sub>s,G\<^sub>s)"         
      using a0 by auto
    then have "\<exists>\<Sigma>'. ((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq (\<Sigma>', \<Sigma>ls)) \<and> (?\<sigma>, (\<Sigma>', \<Sigma>ls)) \<in>\<alpha>"  
      using  sim_elim_cases_c(3)[OF a0] by fastforce
    then have "\<exists>\<Sigma>'. ((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> ((G\<^sub>c', G\<^sub>s'\<^sup>*)\<^sub>\<alpha>) \<and>
                     \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq (\<Sigma>', \<Sigma>ls)) \<and> (?\<sigma>, (\<Sigma>', \<Sigma>ls)) \<in>\<alpha>"
      by (meson G_comp1 a2 a5 a6 subsetD) 
  }
  moreover{       
    assume "C\<^sub>c' = Stuck"
    then have a0:"(\<Gamma>\<^sub>c,(Stuck,?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', ?\<Sigma>),R\<^sub>s,G\<^sub>s)"         
      using a0 by auto
    then have "\<exists>\<Sigma>'. ((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, toSeq (\<Sigma>', \<Sigma>ls)) \<and> (?\<sigma>, (\<Sigma>', \<Sigma>ls)) \<in>\<alpha>"  
      using  sim_elim_cases_c(4)[OF a0] by fastforce
    then have "\<exists>\<Sigma>'. ((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> ((G\<^sub>c', G\<^sub>s'\<^sup>*)\<^sub>\<alpha>) \<and>
                     \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, toSeq (\<Sigma>', \<Sigma>ls)) \<and> (?\<sigma>, (\<Sigma>', \<Sigma>ls)) \<in>\<alpha>"
      by (meson G_comp1 a2 a5 a6 subsetD)
  }
  ultimately show 
    "(((\<sigma>g, \<sigma>l), \<sigma>ls), (\<Sigma>g, \<Sigma>l), \<Sigma>ls) \<in> \<alpha> \<and>
        (\<forall>c\<^sub>c' a b.
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (C\<^sub>c', CRef.toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', CRef.toSeq ((a, b), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', CRef.toSeq ((aa, ba), \<Sigma>ls)) \<and>
                (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> ((G\<^sub>c', G\<^sub>s'\<^sup>*)\<^sub>\<alpha>) \<and>
                ((\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s) \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c',G\<^sub>c') \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>'\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s',G\<^sub>s')))) \<and>
        (\<forall>v c\<^sub>c' a b.
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C\<^sub>c', CRef.toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', CRef.toSeq ((a, b), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                (\<exists>a ab b.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                    (\<exists>ac ad bb.
                        \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, ab, b) \<rightarrow> (ac, ad, bb) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ac, ad, bb) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', CRef.toSeq ((aa, ba), \<Sigma>ls)))) \<and>
                (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> ((G\<^sub>c', G\<^sub>s'\<^sup>*)\<^sub>\<alpha>) \<and>
                ((\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s) \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c',G\<^sub>c') \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>'\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s',G\<^sub>s')))) \<and>
        (\<forall>a b ba aa bb bc.
            ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), ba), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, bb), bc) \<in> ((R\<^sub>c', R\<^sub>s'\<^sup>*)\<^sub>\<alpha>) \<longrightarrow>
            (\<Gamma>\<^sub>c,(C\<^sub>c', (a, b), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', (aa, bb), bc),R\<^sub>s,G\<^sub>s) \<or>
            (\<Gamma>\<^sub>c,(C\<^sub>c', (a, b), ba),R\<^sub>c',G\<^sub>c') \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>'\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', (aa, bb), bc),R\<^sub>s',G\<^sub>s')) \<and>
        (C\<^sub>c' = LanguageCon.com.Skip \<longrightarrow>
         (\<exists>a b. ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (a, b), \<Sigma>ls) \<in> ((G\<^sub>c', G\<^sub>s'\<^sup>*)\<^sub>\<alpha>) \<and>
                (((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<Sigma>ls) \<in> \<gamma>\<^sub>n\<^sub>' \<and>
                \<gamma>\<^sub>n\<^sub>' \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, CRef.toSeq ((a, b), \<Sigma>ls)))) \<and>
        (C\<^sub>c' = LanguageCon.com.Throw \<longrightarrow>
         (\<exists>a b. ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (a, b), \<Sigma>ls) \<in> ((G\<^sub>c', G\<^sub>s'\<^sup>*)\<^sub>\<alpha>) \<and>
                (((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<Sigma>ls) \<in> \<gamma>\<^sub>a\<^sub>' \<and>
                \<gamma>\<^sub>a\<^sub>' \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Throw, CRef.toSeq ((a, b), \<Sigma>ls)))) \<and>
        (\<forall>f. C\<^sub>c' = com.Fault f \<longrightarrow>
             (\<exists>a b. ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (a, b), \<Sigma>ls) \<in> ((G\<^sub>c', G\<^sub>s'\<^sup>*)\<^sub>\<alpha>) \<and>
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (com.Fault f, CRef.toSeq ((a, b), \<Sigma>ls)) \<and>
                    (((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<Sigma>ls) \<in> \<alpha>)) \<and>
        (C\<^sub>c' = com.Stuck \<longrightarrow>
         (\<exists>a b. ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (a, b), \<Sigma>ls) \<in> ((G\<^sub>c', G\<^sub>s'\<^sup>*)\<^sub>\<alpha>) \<and>
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s', CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (com.Stuck, CRef.toSeq ((a, b), \<Sigma>ls)) \<and>
                (((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<Sigma>ls) \<in> \<alpha>))" 
    by auto
qed
  
lemma RGSim_Conseq:
  "\<xi>\<^sub>'\<subseteq>\<xi> \<Longrightarrow>  \<gamma>\<^sub>n \<subseteq> \<gamma>\<^sub>n\<^sub>' \<and> \<gamma>\<^sub>n\<^sub>' \<subseteq> \<alpha> \<Longrightarrow> \<gamma>\<^sub>a \<subseteq> \<gamma>\<^sub>a\<^sub>' \<and> \<gamma>\<^sub>a\<^sub>' \<subseteq> \<alpha> \<Longrightarrow> 
   R\<^sub>s' \<subseteq> R\<^sub>s \<Longrightarrow> R\<^sub>c' \<subseteq> R\<^sub>c \<Longrightarrow> G\<^sub>s \<subseteq> G\<^sub>s' \<Longrightarrow> G\<^sub>c\<subseteq>G\<^sub>c'  \<Longrightarrow> \<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>)\<in>G\<^sub>c \<Longrightarrow>
  (\<Gamma>\<^sub>c,C\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow>
  (\<Gamma>\<^sub>c,C\<^sub>c,R\<^sub>c',G\<^sub>c') \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>'\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>'\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s',G\<^sub>s')"
  unfolding RGSim_pre_def apply (rule,rule,rule)  apply (rule RGSim_Conseq_sound[of \<Gamma>\<^sub>c C\<^sub>c _ R\<^sub>c G\<^sub>c \<alpha> \<gamma>\<^sub>n \<gamma>\<^sub>a])
    by auto    
    

lemma strenrel_sound:
assumes 
   a0:"(\<Gamma>\<^sub>c,(C\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s)" and
   a1:"(\<sigma>,\<Sigma>)\<in>\<alpha>\<^sub>'" and
   a2:"(\<gamma>\<^sub>n \<union> \<gamma>\<^sub>a) \<subseteq> \<alpha>\<^sub>' \<and> \<alpha>\<^sub>' \<subseteq> \<alpha>" and   a8:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>)\<in>G\<^sub>c" and
   a3:"Sta\<^sub>s \<alpha>\<^sub>' (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha>" 
 shows "(\<Gamma>\<^sub>c,(C\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s)"   
  using a0 a1      
 proof (coinduction arbitrary:\<sigma> \<Sigma>  C\<^sub>c C\<^sub>s,clarsimp) 
   fix \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g  \<Sigma>l \<Sigma>ls C\<^sub>c C\<^sub>s
   let ?\<sigma> = "((\<sigma>g::'b, \<sigma>l::'c), \<sigma>ls::'c list)"
   let ?\<Sigma> = "((\<Sigma>g::'f, \<Sigma>l::'g), \<Sigma>ls::'g list)"
   assume a0:"(\<Gamma>\<^sub>c,(C\<^sub>c, ?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, ?\<Sigma>),R\<^sub>s,G\<^sub>s)" and
          a1:"(?\<sigma>, ?\<Sigma>) \<in> \<alpha>\<^sub>'" 
   {
     fix C\<^sub>c' \<sigma>g' \<sigma>l'
     let ?\<sigma>' = "((\<sigma>g'::'b, \<sigma>l'::'c), \<sigma>ls::'c list)"
     assume a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (C\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (C\<^sub>c', toSeq ?\<sigma>')"    
     then have step_alpha:"\<exists>C\<^sub>s' \<Sigma>g' \<Sigma>l'.
       \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s', toSeq (( \<Sigma>g',\<Sigma>l'), \<Sigma>ls)) \<and>
       (?\<sigma>', (( \<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<in> \<alpha> \<and>
       (((?\<sigma>, ?\<sigma>'), (?\<Sigma>, (( \<Sigma>g', \<Sigma>l'), \<Sigma>ls))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
       (\<Gamma>\<^sub>c,(C\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', (( \<Sigma>g', \<Sigma>l'), \<Sigma>ls)),R\<^sub>s,G\<^sub>s)" 
       using dest_sim_tau_step[OF a0 a00]  by auto        
     have "\<exists>C\<^sub>s' \<Sigma>g' \<Sigma>l'.
             \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s', toSeq (( \<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<and>
             (?\<sigma>', (( \<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<in> \<alpha>\<^sub>' \<and>
             ((((?\<sigma>, ?\<sigma>'), (?\<Sigma>, (( \<Sigma>g', \<Sigma>l'), \<Sigma>ls))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
             ((\<Gamma>\<^sub>c,(C\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', (( \<Sigma>g', \<Sigma>l'), \<Sigma>ls)),R\<^sub>s,G\<^sub>s) \<and>
               (?\<sigma>', (( \<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<in> \<alpha>\<^sub>' \<or> 
             (\<Gamma>\<^sub>c,(C\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', (( \<Sigma>g', \<Sigma>l'), \<Sigma>ls)),R\<^sub>s,G\<^sub>s)))" 
      using a1 a3 step_alpha  unfolding Sta\<^sub>s_def related_transitions_def by fast
  } note f1=this
  moreover {
    fix  v C\<^sub>c' \<sigma>g' \<sigma>l'
    let ?\<sigma>' = "((\<sigma>g'::'b, \<sigma>l'::'c), \<sigma>ls::'c list)" 
    assume a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (C\<^sub>c', toSeq ?\<sigma>')"
    then have "\<exists>C\<^sub>s' \<Sigma>'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sup>+ (C\<^sub>s', toSeq (\<Sigma>', \<Sigma>ls)) \<and> 
               (?\<sigma>', (\<Sigma>', \<Sigma>ls)) \<in> \<alpha> \<and>
               (((?\<sigma>, ?\<sigma>'),  ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (\<Gamma>\<^sub>c,(C\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', (\<Sigma>', \<Sigma>ls)),R\<^sub>s,G\<^sub>s)" 
      using dest_sim_ev_step[OF a0 a00]  by auto          
    then have "\<exists>C\<^sub>s' \<Sigma>'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sup>+ (C\<^sub>s', toSeq (\<Sigma>', \<Sigma>ls)) \<and> 
               (?\<sigma>', (\<Sigma>', \<Sigma>ls)) \<in> \<alpha>\<^sub>' \<and>
               (((?\<sigma>, ?\<sigma>'),  ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
               ((\<Gamma>\<^sub>c,(C\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', (\<Sigma>', \<Sigma>ls)),R\<^sub>s,G\<^sub>s) \<and> (?\<sigma>', (\<Sigma>', \<Sigma>ls)) \<in> \<alpha>\<^sub>' \<or> 
                 (\<Gamma>\<^sub>c,(C\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', (\<Sigma>', \<Sigma>ls)),R\<^sub>s,G\<^sub>s))" 
        using a1 a3  unfolding Sta\<^sub>s_def related_transitions_def by fast
    then have  "\<exists>C\<^sub>s' \<Sigma>'.
               (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                      (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s', toSeq (\<Sigma>', \<Sigma>ls)))) \<and>
                (?\<sigma>', (\<Sigma>', \<Sigma>ls)) \<in> \<alpha>\<^sub>' \<and>
               (((?\<sigma>, ?\<sigma>'),  ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
               ((\<Gamma>\<^sub>c,(C\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', (\<Sigma>', \<Sigma>ls)),R\<^sub>s,G\<^sub>s) \<and> (?\<sigma>', (\<Sigma>', \<Sigma>ls)) \<in> \<alpha>\<^sub>' \<or> 
                 (\<Gamma>\<^sub>c,(C\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', (\<Sigma>', \<Sigma>ls)),R\<^sub>s,G\<^sub>s))" 
      by fast      
  } note f2=this
  moreover{
    fix \<sigma>g' \<sigma>l' \<sigma>ls' \<Sigma>g' \<Sigma>l' \<Sigma>ls'
    let ?\<Sigma>' = "((\<Sigma>g'::'f, \<Sigma>l'::'g), \<Sigma>ls'::'g list)"
    let ?\<sigma>' = "((\<sigma>g'::'b, \<sigma>l'::'c), \<sigma>ls'::'c list)"
    assume a00:"(((?\<sigma>, ?\<sigma>'), ?\<Sigma>, ?\<Sigma>') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>')"   
    then have a00':"((?\<sigma>, ?\<sigma>'), ?\<Sigma>, ?\<Sigma>') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> " 
      using  a2  unfolding Sta\<^sub>s_def related_transitions_def by fast  
    moreover have  "(?\<sigma>', ?\<Sigma>')\<in>\<alpha>\<^sub>'" using a00 unfolding related_transitions_def by auto
    ultimately have "(\<Gamma>\<^sub>c,(C\<^sub>c, ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, ?\<Sigma>'),R\<^sub>s,G\<^sub>s) \<and> (?\<sigma>', ?\<Sigma>')\<in>\<alpha>\<^sub>' \<or> 
          (\<Gamma>\<^sub>c,(C\<^sub>c, ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, ?\<Sigma>'),R\<^sub>s,G\<^sub>s)" 
      using dest_sim_env_step[OF a0 a00'] by auto    
    (* then have "(\<Gamma>\<^sub>c,(C\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', ?\<Sigma>'),R\<^sub>s,G\<^sub>s) \<or>
           (\<Gamma>\<^sub>c,(C\<^sub>c', ?\<sigma>'),R\<^sub>c',G\<^sub>c') \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>'\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', ?\<Sigma>'),R\<^sub>s',G\<^sub>s')"  by auto *)
  } note f3=this
  moreover{       
    assume a00:"C\<^sub>c = Skip"
    then have a0:"(\<Gamma>\<^sub>c,(Skip,?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, ?\<Sigma>),R\<^sub>s,G\<^sub>s)"         
      using a0 by auto
    then obtain \<Sigma>' where step_alpha:" ((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (?\<sigma>, (\<Sigma>', \<Sigma>ls)) \<in> \<gamma>\<^sub>n \<and> \<gamma>\<^sub>n \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeq (\<Sigma>',\<Sigma>ls))" 
      using sim_elim_cases_c(1)[OF a0] by force
    moreover have "(?\<sigma>, (\<Sigma>', \<Sigma>ls))\<in>\<alpha>\<^sub>'" using  a1 a3 calculation 
      unfolding Sta\<^sub>s_def  by blast
    moreover have "((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>')"
      using   a1 calculation unfolding related_transitions_def by auto
    ultimately have   "\<exists>\<Sigma>'. (((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                     (?\<sigma>, (\<Sigma>',\<Sigma>ls)) \<in> \<gamma>\<^sub>n \<and> \<gamma>\<^sub>n \<subseteq> \<alpha>\<^sub>' \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeq (\<Sigma>',\<Sigma>ls))"
      using a2  by blast
  }  note f4=this
  moreover{   
    assume a00:"C\<^sub>c = Throw "
    then have a0:"(\<Gamma>\<^sub>c,(Throw,?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, ?\<Sigma>),R\<^sub>s,G\<^sub>s)"         
      using a0 by auto
    then obtain \<Sigma>' where "((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
             (?\<sigma>, (\<Sigma>', \<Sigma>ls)) \<in> \<gamma>\<^sub>a \<and> \<gamma>\<^sub>a \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, toSeq (\<Sigma>', \<Sigma>ls))"  
      using  sim_elim_cases_c(2)[OF a0] by force
    moreover have "(?\<sigma>, (\<Sigma>', \<Sigma>ls))\<in>\<alpha>\<^sub>'" using  a1 a3 calculation 
      unfolding Sta\<^sub>s_def  by blast
    moreover have "((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>')"
      using   a1 calculation unfolding related_transitions_def by auto
    ultimately have "\<exists>\<Sigma>'. (((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                     (?\<sigma>, (\<Sigma>',\<Sigma>ls)) \<in> \<gamma>\<^sub>a \<and> \<gamma>\<^sub>a \<subseteq> \<alpha>\<^sub>' \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, toSeq (\<Sigma>',\<Sigma>ls))"
       using a2  by blast   
  } note f5=this
  moreover{   
    fix f
    assume "C\<^sub>c = Fault f"
    then have a0:"(\<Gamma>\<^sub>c,(Fault f,?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, ?\<Sigma>),R\<^sub>s,G\<^sub>s)"         
      using a0 by auto
    then obtain \<Sigma>' where "((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq (\<Sigma>', \<Sigma>ls)) \<and> (?\<sigma>, (\<Sigma>', \<Sigma>ls)) \<in>\<alpha>"  
      using  sim_elim_cases_c(3)[OF a0] by fastforce
    moreover have "(?\<sigma>, (\<Sigma>', \<Sigma>ls))\<in>\<alpha>\<^sub>'" using  a1 a3 calculation 
      unfolding Sta\<^sub>s_def  by blast
    moreover have "((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>')"
      using   a1 calculation unfolding related_transitions_def by auto
    ultimately have "\<exists>\<Sigma>'. (((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                      \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq (\<Sigma>',\<Sigma>ls)) \<and> (?\<sigma>, (\<Sigma>', \<Sigma>ls))\<in>\<alpha>\<^sub>'"
      by blast 
  }  note f6=this
  moreover{       
    assume "C\<^sub>c = Stuck"
    then have a0:"(\<Gamma>\<^sub>c,(Stuck,?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, ?\<Sigma>),R\<^sub>s,G\<^sub>s)"         
      using a0 by auto
    then obtain \<Sigma>' where "((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, toSeq (\<Sigma>', \<Sigma>ls)) \<and> (?\<sigma>, (\<Sigma>', \<Sigma>ls)) \<in>\<alpha>"  
      using  sim_elim_cases_c(4)[OF a0] by fastforce
    moreover have "(?\<sigma>, (\<Sigma>', \<Sigma>ls))\<in>\<alpha>\<^sub>'" using  a1 a3 calculation 
      unfolding Sta\<^sub>s_def  by blast
    moreover have "((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>')"
      using   a1 calculation unfolding related_transitions_def by auto
    ultimately have "\<exists>\<Sigma>'. (((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                      \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, toSeq (\<Sigma>',\<Sigma>ls)) \<and> (?\<sigma>, (\<Sigma>', \<Sigma>ls))\<in>\<alpha>\<^sub>'"
       using a2  by blast
   }  note f7=this
   ultimately show 
     "(\<forall>c\<^sub>c' a b.
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (C\<^sub>c, CRef.toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', CRef.toSeq ((a, b), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', CRef.toSeq ((aa, ba), \<Sigma>ls)) \<and>
                (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha>\<^sub>' \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                ((\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                 (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s) \<and> (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha>\<^sub>' \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
                 (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))) \<and>
        (\<forall>v c\<^sub>c' a b. \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C\<^sub>c, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((a, b), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                (\<exists>a ab b.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                    (\<exists>ac ad bb. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, ab, b) \<rightarrow> (ac, ad, bb) \<and>
                        \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ac, ad, bb) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((aa, ba), \<Sigma>ls)))) \<and>
                (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha>\<^sub>' \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                ((\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s) \<and> 
                (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha>\<^sub>' \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))) \<and>
        (\<forall>a b ba aa bb bc.
            ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), ba), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, bb), bc) \<in> ((R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<longrightarrow>
            (\<Gamma>\<^sub>c,(C\<^sub>c, (a, b), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, (aa, bb), bc),R\<^sub>s,G\<^sub>s) \<and>
            (((a, b), ba), (aa, bb), bc) \<in> \<alpha>\<^sub>' \<or>
            (\<Gamma>\<^sub>c,(C\<^sub>c, (a, b), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
            (\<Gamma>\<^sub>s,(C\<^sub>s, (aa, bb), bc),R\<^sub>s,G\<^sub>s)) \<and>
        (C\<^sub>c = Skip \<longrightarrow>
         (\<exists>a b. ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (a, b), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                (((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<Sigma>ls) \<in> \<gamma>\<^sub>n \<and> \<gamma>\<^sub>n \<subseteq> \<alpha>\<^sub>' \<and>
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeq ((a, b), \<Sigma>ls)))) \<and>
        (C\<^sub>c = Throw \<longrightarrow>
         (\<exists>a b. ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (a, b), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                (((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<Sigma>ls) \<in> \<gamma>\<^sub>a \<and> \<gamma>\<^sub>a \<subseteq> \<alpha>\<^sub>' \<and>
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, toSeq ((a, b), \<Sigma>ls)))) \<and>
        (\<forall>f. C\<^sub>c = Fault f \<longrightarrow>
             (\<exists>a b. ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (a, b), \<Sigma>ls)
                    \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq ((a, b), \<Sigma>ls)) \<and>
                    (((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<Sigma>ls) \<in> \<alpha>\<^sub>')) \<and>
        (C\<^sub>c = com.Stuck \<longrightarrow>
         (\<exists>a b. ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (a, b), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, toSeq ((a, b), \<Sigma>ls)) \<and>
                (((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<Sigma>ls) \<in> \<alpha>\<^sub>'))" by auto     
qed
  
 
lemma strenrel:
  "(\<Gamma>\<^sub>c,C\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow>
  (\<xi> \<union> \<gamma>\<^sub>n \<union> \<gamma>\<^sub>a) \<subseteq> \<alpha>\<^sub>' \<and> \<alpha>\<^sub>' \<subseteq> \<alpha> \<Longrightarrow>
  Sta\<^sub>s \<alpha>\<^sub>' (G\<^sub>c,G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<Longrightarrow>    \<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow>(\<sigma>,\<sigma>)\<in>G\<^sub>c \<Longrightarrow>
   (\<Gamma>\<^sub>c,C\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def apply (rule, rule, rule) apply (rule strenrel_sound)   
  by auto
    
 lemma weakenrel_sound:
assumes 
   a0:"(\<Gamma>\<^sub>c,(C\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s)" and
   a1:"\<alpha> \<subseteq> \<alpha>\<^sub>'" and
   a2:" Sta\<^sub>s \<alpha> (R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>'" and a8:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>,\<sigma>)\<in>G\<^sub>c"
 shows "(\<Gamma>\<^sub>c,(C\<^sub>c, \<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, \<Sigma>),R\<^sub>s,G\<^sub>s)"   
   using a0  
 proof (coinduction arbitrary:\<sigma> \<Sigma>  C\<^sub>c C\<^sub>s,clarsimp) 
   fix \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g  \<Sigma>l \<Sigma>ls C\<^sub>c C\<^sub>s 
   let ?\<sigma> = "((\<sigma>g::'b, \<sigma>l::'c), \<sigma>ls::'c list)"
   let ?\<Sigma> = "((\<Sigma>g::'f, \<Sigma>l::'g), \<Sigma>ls::'g list)"
   assume a0:"(\<Gamma>\<^sub>c,(C\<^sub>c, ?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, ?\<Sigma>),R\<^sub>s,G\<^sub>s)"   
   have alpha_rel:"(((\<sigma>g, \<sigma>l), \<sigma>ls), (\<Sigma>g, \<Sigma>l), \<Sigma>ls) \<in> \<alpha>\<^sub>'" 
     using dest_sim_alpha[OF a0] using a1 by fastforce   
   moreover{
     fix C\<^sub>c' \<sigma>g' \<sigma>l'
     let ?\<sigma>' = "((\<sigma>g'::'b, \<sigma>l'::'c), \<sigma>ls::'c list)"
     assume a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (C\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (C\<^sub>c', toSeq ?\<sigma>')"             
     then obtain C\<^sub>s' \<Sigma>g' \<Sigma>l' where step_alpha:"
       \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s', toSeq (( \<Sigma>g',\<Sigma>l'), \<Sigma>ls)) \<and>
       (?\<sigma>', (( \<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<in> \<alpha> \<and>
       (((?\<sigma>, ?\<sigma>'), (?\<Sigma>, (( \<Sigma>g', \<Sigma>l'), \<Sigma>ls))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
       (\<Gamma>\<^sub>c,(C\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', (( \<Sigma>g', \<Sigma>l'), \<Sigma>ls)),R\<^sub>s,G\<^sub>s)" 
       using dest_sim_tau_step[OF a0 a00] by auto 
     moreover have "(?\<sigma>',(( \<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<in> \<alpha>\<^sub>'" using a1 calculation by auto
     moreover have "(((?\<sigma>, ?\<sigma>'), (?\<Sigma>, (( \<Sigma>g', \<Sigma>l'), \<Sigma>ls))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>')"
       using step_alpha  a1   unfolding related_transitions_def  by auto
     ultimately have "\<exists>c\<^sub>s' aa ba.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((aa, ba), \<Sigma>ls)) \<and>
                (?\<sigma>',(( aa, ba), \<Sigma>ls)) \<in> \<alpha>\<^sub>' \<and>
                ((?\<sigma>, ?\<sigma>'), (((\<Sigma>g, \<Sigma>l), \<Sigma>ls), ((aa, ba), \<Sigma>ls))) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                ((\<Gamma>\<^sub>c,(C\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s) \<or> 
                  (\<Gamma>\<^sub>c,(C\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s))"       
       by auto
   } note f1=this
   moreover{
     fix  v C\<^sub>c' \<sigma>g' \<sigma>l'
     let ?\<sigma>' = "((\<sigma>g'::'b, \<sigma>l'::'c), \<sigma>ls::'c list)" 
     assume a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C\<^sub>c, toSeq ?\<sigma>) \<rightarrow> (C\<^sub>c', toSeq ?\<sigma>')"     
     then obtain C\<^sub>s' \<Sigma>' where step_alpha:" 
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sup>+ (C\<^sub>s', toSeq (\<Sigma>', \<Sigma>ls)) \<and> 
               (?\<sigma>', (\<Sigma>', \<Sigma>ls)) \<in> \<alpha> \<and>
               (((?\<sigma>, ?\<sigma>'),  ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (\<Gamma>\<^sub>c,(C\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', (\<Sigma>', \<Sigma>ls)),R\<^sub>s,G\<^sub>s)" 
        using dest_sim_ev_step[OF a0 a00]  by fastforce
      moreover have "(?\<sigma>', (\<Sigma>', \<Sigma>ls)) \<in> \<alpha>\<^sub>'" using a1 calculation by auto
      moreover have "((?\<sigma>, ?\<sigma>'), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>'"
        using step_alpha  a1  unfolding related_transitions_def  by fast
      ultimately have " 
               \<exists>C\<^sub>s' \<Sigma>'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sup>+ (C\<^sub>s', toSeq (\<Sigma>', \<Sigma>ls)) \<and> 
               (?\<sigma>', (\<Sigma>', \<Sigma>ls)) \<in> \<alpha>\<^sub>' \<and>
               (((?\<sigma>, ?\<sigma>'),  ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
               ((\<Gamma>\<^sub>c,(C\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', (\<Sigma>', \<Sigma>ls)),R\<^sub>s,G\<^sub>s) \<and> (?\<sigma>', (\<Sigma>', \<Sigma>ls)) \<in> \<alpha>\<^sub>' \<or> 
                 (\<Gamma>\<^sub>c,(C\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', (\<Sigma>', \<Sigma>ls)),R\<^sub>s,G\<^sub>s))" by fastforce
       then have  "\<exists>C\<^sub>s' \<Sigma>'.
               (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                      (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (C\<^sub>s', toSeq (\<Sigma>', \<Sigma>ls)))) \<and>
                (?\<sigma>', (\<Sigma>', \<Sigma>ls)) \<in> \<alpha>\<^sub>' \<and>
               (((?\<sigma>, ?\<sigma>'),  ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
               ((\<Gamma>\<^sub>c,(C\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', (\<Sigma>', \<Sigma>ls)),R\<^sub>s,G\<^sub>s) \<and> (?\<sigma>', (\<Sigma>', \<Sigma>ls)) \<in> \<alpha>\<^sub>' \<or> 
                 (\<Gamma>\<^sub>c,(C\<^sub>c', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s', (\<Sigma>', \<Sigma>ls)),R\<^sub>s,G\<^sub>s))" by fast
   }  note f2=this
   moreover{
     fix \<sigma>g' \<sigma>l' \<sigma>ls' \<Sigma>g' \<Sigma>l' \<Sigma>ls'
     let ?\<Sigma>' = "((\<Sigma>g'::'f, \<Sigma>l'::'g), \<Sigma>ls'::'g list)"
     let ?\<sigma>' = "((\<sigma>g'::'b, \<sigma>l'::'c), \<sigma>ls'::'c list)"
     assume a00:"(((?\<sigma>, ?\<sigma>'), ?\<Sigma>, ?\<Sigma>') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>')"  
     have "(?\<sigma>,?\<Sigma>)\<in>\<alpha>" using dest_sim_alpha[OF a0] calculation by auto
     then have a00':"((?\<sigma>, ?\<sigma>'), ?\<Sigma>, ?\<Sigma>') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> " 
       using  a00 a2  unfolding Sta\<^sub>s_def related_transitions_def by fast  
     moreover have  "(?\<sigma>', ?\<Sigma>')\<in>\<alpha>\<^sub>'" using a00 unfolding related_transitions_def by auto
     ultimately have "(\<Gamma>\<^sub>c,(C\<^sub>c, ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, ?\<Sigma>'),R\<^sub>s,G\<^sub>s) \<and> (?\<sigma>', ?\<Sigma>')\<in>\<alpha>\<^sub>' \<or> 
          (\<Gamma>\<^sub>c,(C\<^sub>c, ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, ?\<Sigma>'),R\<^sub>s,G\<^sub>s)" 
       using dest_sim_env_step[OF a0 a00'] by auto              
    }  note f3=this
    moreover{       
      assume a00:"C\<^sub>c = Skip"
      then have a0:"(\<Gamma>\<^sub>c,(Skip,?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, ?\<Sigma>),R\<^sub>s,G\<^sub>s)"         
        using a0 by auto
      then obtain \<Sigma>' where step_alpha:" ((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (?\<sigma>, (\<Sigma>', \<Sigma>ls)) \<in> \<gamma>\<^sub>n \<and> \<gamma>\<^sub>n \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeq (\<Sigma>',\<Sigma>ls))" 
        using sim_elim_cases_c(1)[OF a0] by force
      moreover have "(?\<sigma>, (\<Sigma>', \<Sigma>ls))\<in>\<alpha>\<^sub>'" using  a1  calculation 
        unfolding Sta\<^sub>s_def  by blast
      moreover have "((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>')"
        using   a1 calculation unfolding related_transitions_def by auto
      ultimately have   "\<exists>\<Sigma>'. (((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                       (?\<sigma>, (\<Sigma>',\<Sigma>ls)) \<in> \<gamma>\<^sub>n \<and> \<gamma>\<^sub>n \<subseteq> \<alpha>\<^sub>' \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeq (\<Sigma>',\<Sigma>ls))"
        using a1  by blast
    }  note f4=this
    moreover{   
      assume a00:"C\<^sub>c = Throw "
      then have a0:"(\<Gamma>\<^sub>c,(Throw,?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, ?\<Sigma>),R\<^sub>s,G\<^sub>s)"         
        using a0 by auto
      then obtain \<Sigma>' where "((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (?\<sigma>, (\<Sigma>', \<Sigma>ls)) \<in> \<gamma>\<^sub>a \<and> \<gamma>\<^sub>a \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, toSeq (\<Sigma>', \<Sigma>ls))"  
        using  sim_elim_cases_c(2)[OF a0] by force
      moreover have "(?\<sigma>, (\<Sigma>', \<Sigma>ls))\<in>\<alpha>\<^sub>'" using  a1 calculation 
        unfolding Sta\<^sub>s_def  by blast
      moreover have "((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>')"
        using   a1 calculation unfolding related_transitions_def by auto
      ultimately have "\<exists>\<Sigma>'. (((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                       (?\<sigma>, (\<Sigma>',\<Sigma>ls)) \<in> \<gamma>\<^sub>a \<and> \<gamma>\<^sub>a \<subseteq> \<alpha>\<^sub>' \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, toSeq (\<Sigma>',\<Sigma>ls))"
         using a1  by blast   
    } note f5=this
    moreover{   
      fix f
      assume "C\<^sub>c = Fault f"
      then have a0:"(\<Gamma>\<^sub>c,(Fault f,?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, ?\<Sigma>),R\<^sub>s,G\<^sub>s)"         
        using a0 by auto
      then obtain \<Sigma>' where "((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq (\<Sigma>', \<Sigma>ls)) \<and> (?\<sigma>, (\<Sigma>', \<Sigma>ls)) \<in>\<alpha>"  
        using  sim_elim_cases_c(3)[OF a0] by fastforce
      moreover have "(?\<sigma>, (\<Sigma>', \<Sigma>ls))\<in>\<alpha>\<^sub>'" using  a1 calculation 
        unfolding Sta\<^sub>s_def  by blast
      moreover have "((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>')"
        using   a1 calculation unfolding related_transitions_def by auto
      ultimately have "\<exists>\<Sigma>'. (((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                        \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq (\<Sigma>',\<Sigma>ls)) \<and> (?\<sigma>, (\<Sigma>', \<Sigma>ls))\<in>\<alpha>\<^sub>'"
         by blast 
    }  note f6=this
    moreover{       
      assume "C\<^sub>c = Stuck"
      then have a0:"(\<Gamma>\<^sub>c,(Stuck,?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, ?\<Sigma>),R\<^sub>s,G\<^sub>s)"         
        using a0 by auto
      then obtain \<Sigma>' where "((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, toSeq (\<Sigma>', \<Sigma>ls)) \<and> (?\<sigma>, (\<Sigma>', \<Sigma>ls)) \<in>\<alpha>"  
        using  sim_elim_cases_c(4)[OF a0] by fastforce
      moreover have "(?\<sigma>, (\<Sigma>', \<Sigma>ls))\<in>\<alpha>\<^sub>'" using  a1  calculation 
        unfolding Sta\<^sub>s_def  by blast
      moreover have "((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>')"
        using   a1 calculation unfolding related_transitions_def by auto
      ultimately have "\<exists>\<Sigma>'. (((?\<sigma>, ?\<sigma>), ?\<Sigma>, (\<Sigma>', \<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                        \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ?\<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, toSeq (\<Sigma>',\<Sigma>ls)) \<and> (?\<sigma>, (\<Sigma>', \<Sigma>ls))\<in>\<alpha>\<^sub>'"
         by blast
     }  note f7=this 
    show 
     "(((\<sigma>g, \<sigma>l), \<sigma>ls), (\<Sigma>g, \<Sigma>l), \<Sigma>ls) \<in> \<alpha>\<^sub>' \<and>
        (\<forall>c\<^sub>c' a b.
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (C\<^sub>c, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((a, b), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((aa, ba), \<Sigma>ls)) \<and>
                (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha>\<^sub>' \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                ((\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s) \<or> 
                  (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))) \<and>
        (\<forall>v c\<^sub>c' a b.
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C\<^sub>c, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((a, b), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                (\<exists>a ab b.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                    (\<exists>ac ad bb.
                        \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, ab, b) \<rightarrow> (ac, ad, bb) \<and>
                        \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ac, ad, bb) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((aa, ba), \<Sigma>ls)))) \<and>
                (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha>\<^sub>' \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                ((\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s) \<or> 
                  (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))) \<and>
        (\<forall>a b ba aa bb bc.
            ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), ba), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, bb), bc) \<in> ((R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<longrightarrow>
            (\<Gamma>\<^sub>c,(C\<^sub>c, (a, b), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, (aa, bb), bc),R\<^sub>s,G\<^sub>s) \<or>
            (\<Gamma>\<^sub>c,(C\<^sub>c, (a, b), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(C\<^sub>s, (aa, bb), bc),R\<^sub>s,G\<^sub>s)) \<and>
        (C\<^sub>c = Skip \<longrightarrow>
         (\<exists>a b. ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (a, b), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                (((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<Sigma>ls) \<in> \<gamma>\<^sub>n \<and> \<gamma>\<^sub>n \<subseteq> \<alpha>\<^sub>' \<and>
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeq ((a, b), \<Sigma>ls)))) \<and>
        (C\<^sub>c = Throw \<longrightarrow>
         (\<exists>a b. ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (a, b), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                (((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<Sigma>ls) \<in> \<gamma>\<^sub>a \<and> \<gamma>\<^sub>a \<subseteq> \<alpha>\<^sub>' \<and>
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, toSeq ((a, b), \<Sigma>ls)))) \<and>
        (\<forall>f. C\<^sub>c = Fault f \<longrightarrow>
             (\<exists>a b. ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (a, b), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq ((a, b), \<Sigma>ls)) \<and>
                    (((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<Sigma>ls) \<in> \<alpha>\<^sub>')) \<and>
        (C\<^sub>c = Stuck \<longrightarrow>
         (\<exists>a b. ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (a, b), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>') \<and>
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (C\<^sub>s, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, toSeq ((a, b), \<Sigma>ls)) \<and>
                (((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<Sigma>ls) \<in> \<alpha>\<^sub>'))" 
 apply (rule conjId)+
      using  f4 f5 f6 f7 apply auto[4] 
      using f3 f2  apply (fast, fast) 
      using alpha_rel f1 by auto         
qed   
    
 lemma weakenrel:
  "(\<Gamma>\<^sub>c,C\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow>
  \<alpha> \<subseteq> \<alpha>\<^sub>' \<Longrightarrow> Sta\<^sub>s \<alpha> (R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>\<^sub>' \<Longrightarrow>  \<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow>(\<sigma>,\<sigma>)\<in>G\<^sub>c \<Longrightarrow>
   (\<Gamma>\<^sub>c,C\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>'\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def apply (rule, rule, rule) apply (rule weakenrel_sound)     
  by auto
 

primrec state_mod :: "('s,'p,'f,'e) com \<Rightarrow> bool"
  where 
"state_mod (Basic _ _)  = True"
|"state_mod (Spec _ _)  = True"
|"state_mod (Await _ _ _)  = True"
|"state_mod Skip = False"
  |"state_mod (Seq _ _) = False"    
  |"state_mod (Cond _ _ _) = False"
  | "state_mod (While _ _) = False"
  | "state_mod (Call _) = False"
  | "state_mod (DynCom _) = False" 
  | "state_mod (Guard _ _ _) =False" 
  | "state_mod Throw = False"
  | "state_mod (Catch _ _) = False"
  | "state_mod (Stuck  ) = False"
  | "state_mod (Fault _ ) = False"


primrec label :: "('s,'p,'f,'e) com \<Rightarrow> 'e option"
  where
"label (Basic _ l)  = l"
|"label (Spec _ l)  = l"
|"label (Await _ _ l)  = l"
|"label Skip = None"
  |"label (Seq c1 c2) = (if (c1\<noteq>Skip \<and> c1\<noteq>Throw \<and> c1\<noteq>Stuck \<and> (\<forall>f. c1 \<noteq> Fault f)) then label c1 else None)"    
  |"label (Cond _ _ _) = None"
  | "label (While _ _) = None"
  | "label (Call _) = None"
  | "label (DynCom _) = None" 
  | "label (Guard _ _ _) =None" 
  | "label Throw = None"
  | "label (Catch c1 c2) = (if (c1\<noteq>Skip \<and> c1\<noteq>Throw) then label c1 else None)"
  | "label (Stuck  ) = None"
  | "label (Fault _ ) = None"

lemma 
  assumes 
     a0:"(\<And>C'. \<Gamma>\<turnstile>\<^sub>c\<^sub>e (C1, s) \<rightarrow> (C', s') \<Longrightarrow> label C1 = e)" and          
     a2:"\<Gamma>\<turnstile>\<^sub>c\<^sub>e (LanguageCon.com.Seq C1 C2,  s) \<rightarrow> (C', s')" and
     a3:"l = label C1"    
  shows "label C1 = e"
proof (cases C1)
  case Skip then show ?thesis using evstepc_elim_seq(3)[OF a2] a0 
    by fastforce  
next
  case (Basic x21 x22)   
  then show ?thesis using evstepc_elim_seq(3)[OF a2] a0 
    by fastforce  
next
  case (Spec x31 x32)    
  then show ?thesis using evstepc_elim_seq(3)[OF a2] a0 
    by fastforce     
next
  case (Seq x41 x42)      
  then show ?thesis using evstepc_elim_seq(3)[OF a2] a0 
    by fastforce
    
next
case (Cond x51 x52 x53)
  then show ?thesis using evstepc_elim_seq(3)[OF a2] a0 
    by fastforce
next
  case (While x61 x62)
  then show ?thesis  using evstepc_elim_seq(3)[OF a2] a0  
    by fastforce
next
  case (Call x7) then show ?thesis  using evstepc_elim_seq(3)[OF a2] a0  
    by fastforce
next
  case (DynCom x8) then show ?thesis  using evstepc_elim_seq(3)[OF a2] a0  
    by fastforce
next
  case (Guard x91 x92 x93)
    then show ?thesis  using evstepc_elim_seq(3)[OF a2] a0  
    by fastforce
next
  case Throw
  then show ?thesis  using evstepc_elim_seq(3)[OF a2] a0  
    by fastforce
next
  case (Catch x111 x112)
  then show ?thesis  using evstepc_elim_seq(3)[OF a2] a0  
    by fastforce
next
  case (Await x121 x122 x123)
  then show ?thesis  using evstepc_elim_seq(3)[OF a2] a0  
    by fastforce
next
  case Stuck then show ?thesis  using evstepc_elim_seq(3)[OF a2] a0  
    by fastforce
next 
  case (Fault f) then show ?thesis  using evstepc_elim_seq(3)[OF a2] a0  
    by fastforce
qed


lemma label_step:"label C = l \<Longrightarrow> \<Gamma>\<turnstile>\<^sub>c\<^sub>e (C,  s) \<rightarrow> (C',s') \<Longrightarrow>
      l = e"
  apply (induction C arbitrary: C')  apply auto  
  by (fastforce elim: stepc_elim_cases1)+
                              



primrec com_step_n' ::"('s,'p,'f,'e) com \<Rightarrow> 's \<Rightarrow> ('s,'p,'f,'e) body \<Rightarrow> 's set"
  where
"com_step_n'  (Basic f l) s \<Gamma> = {s'. s' = f s}"
|"com_step_n' (Spec r l) s \<Gamma> = {s'. ((s,s')\<in> r) \<or> ((\<nexists>s1.(s, s1)\<in>r) \<and> s' = s)}"
|"com_step_n' (Await b c l) s \<Gamma> = 
      {t. (s \<in> b \<and> (\<exists>t'. \<Gamma>\<^sub>\<not>\<^sub>a\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t' \<and> 
                         (t' = Normal t \<or> t' = Abrupt t \<or> 
                         (t' = xstate.Stuck \<and> t=s) \<or> (\<exists>f. t' = xstate.Fault f \<and> t = s) )))}"
(* |"com_step Skip s \<Gamma> = {Normal s} "
|"com_step (Seq _ _) s \<Gamma> = {Normal s}"    
|"com_step (Cond _ _ _) s \<Gamma> = {Normal s}"
| "com_step (While _ _) s \<Gamma> = {Normal s}"
| "com_step (Call _) s \<Gamma> = {Normal s}" 
| "com_step (DynCom _) s \<Gamma> = {Normal s}" 
| "com_step (Guard _ _ _) s \<Gamma> = {Normal s}" 
| "com_step Throw s \<Gamma> = {Normal s}"
| "com_step (Catch _ _) s \<Gamma> = {Normal s}"  *)

primrec com_step ::"('s,'p,'f,'e) com \<Rightarrow> 's \<Rightarrow> ('s,'p,'f,'e) body \<Rightarrow> (('s,'p,'f,'e) com \<times> 's) set"
  where
"com_step  (Basic f l) s \<Gamma> = {(c,s'). c = Skip \<and> s' = f s}"
|"com_step (Spec r l) s \<Gamma> = {(c,s'). ((s,s')\<in> r \<and> c=Skip) \<or> ((\<nexists>s1.(s, s1)\<in>r) \<and> s' = s \<and> c=Stuck)}"
|"com_step (Await b c l) s \<Gamma> = 
      {(c',t). (s \<in> b \<and> (\<exists>t'. \<Gamma>\<^sub>\<not>\<^sub>a\<turnstile>\<langle>c,Normal s\<rangle> \<Rightarrow> t' \<and> 
                         ((t' = Normal t \<and> c' = Skip) \<or> (t' = Abrupt t \<and> c' = Throw) \<or> 
                         (t' = xstate.Stuck \<and> t=s \<and> c' = Stuck) \<or> 
                         (\<exists>f. t' = xstate.Fault f \<and> t = s \<and> c' = Fault f) )))}"

lemma com_step_Basic:
  assumes a0:"(c,s') \<in> com_step P s \<Gamma>" and
        a1:"(\<exists> f. P = Basic f l) " 
  shows  "\<Gamma>\<turnstile>\<^sub>c\<^sub>l (P, s) \<rightarrow> (c, s')" 
proof-
  show ?thesis using a0 a1 
    apply auto 
    by (force intro: stepc_stepce_unique stepce.Basicc)    
qed 

lemma com_step_Spec_r:
  assumes a0:"(c,s') \<in> com_step P s \<Gamma>" and
        a1:"P = Spec r l"
  shows  "\<Gamma>\<turnstile>\<^sub>c\<^sub>l (P, s) \<rightarrow> (c, s')" 
proof-
  show ?thesis using a0 a1 
    apply auto                                  
    by (force intro: stepc_stepce_unique stepce.Specc stepce.SpecStuckc)+      
qed 


lemma com_step_await:
  assumes a0:"(c',s') \<in> com_step P s \<Gamma>" and
        a1:" P = Await b c l"
  shows  "\<Gamma>\<turnstile>\<^sub>c\<^sub>l (P, s) \<rightarrow> (c', s')" 
proof-
  show ?thesis using a0 a1 
    apply auto                                  
    by (meson  stepce.Awaitc stepc_stepce_unique AwaitAbruptc AwaitStuckc AwaitFaultc)+      
qed

lemma Spec_r_com_step:
  assumes a0:"\<Gamma>\<turnstile>\<^sub>c\<^sub>l (Spec r l, s) \<rightarrow> (c, s')"        
  shows  "(c,s') \<in> com_step (Spec r l) s \<Gamma>" 
proof-
  have "c = Skip \<or> c = Stuck"
    by (meson assms spec_skip stepce_stepc)
  moreover { assume a00:"c = Skip"
    then have "(s,s') \<in> r" using a0 stepc_elim_cases1(6) by fastforce
    then have ?thesis using a0 a00  
      by auto      
  }
  moreover { assume a00:"c = Stuck"
    then have "\<forall>t. (s,t) \<notin> r \<and> s = s'" using a0 stepc_elim_cases1(6)
      by (metis LanguageCon.com.distinct(13) prod.inject)
    then have ?thesis using a0 a00 by auto       
  }
  ultimately show ?thesis by auto
qed

lemma Basic_com_step:
  assumes a0:"\<Gamma>\<turnstile>\<^sub>c\<^sub>l (Basic f l, s) \<rightarrow> (c, s')"        
  shows  "(c,s') \<in> com_step (Basic f l) s \<Gamma>" 
    using assms stepc_elim_cases1(5) a0
    by fastforce

lemma await_com_step:
  assumes a0:"\<Gamma>\<turnstile>\<^sub>c\<^sub>l (Await b c l, s) \<rightarrow> (c', s')"         
  shows  "(c',s') \<in> com_step (Await b c l) s \<Gamma>"
proof-
  have b:"s \<in> b" using stepc_elim_cases1(10)[OF a0] by fastforce
  have "c' = Skip \<or> c' = Throw \<or> c' = Stuck \<or> (\<exists>f. c' = Fault f)"
    using stepc_elim_cases1(10)[OF a0] by fastforce
  then show ?thesis using b a0 by (auto elim: stepc_elim_cases(15,16,17,18) )
qed


(* 
lemma com_step_n:"s' \<in> com_step P s \<Gamma> \<Longrightarrow> \<not>(\<exists>t'. s' = Abrupt t') \<Longrightarrow> 
                 (\<exists>b c l. P = Await b c l \<and> s\<in>b) \<Longrightarrow> \<exists>P' l. \<Gamma>\<turnstile>\<^sub>c\<^sub>l (P, s) \<rightarrow> (P', s')"  
  apply auto
   by (meson stepc.Awaitc stepc_stepce_unique)
  
lemma com_step_b:"s' \<in> com_step P s \<Gamma> \<Longrightarrow>  s' = Abrupt t' \<Longrightarrow> (\<exists>b c l. P = Await b c l \<and> s\<in>b) \<Longrightarrow> \<exists>P' l. \<Gamma>\<turnstile>\<^sub>c\<^sub>l (P, Normal s) \<rightarrow> (P', Normal t')"  
  apply auto
   by (meson stepc.AwaitAbruptc stepc_stepce_unique)


lemma "\<forall>\<sigma> \<sigma>' \<Sigma> . (Normal \<sigma>, Normal \<Sigma>)\<in>\<xi> \<and> \<sigma>' \<in> com_step  C \<sigma>  \<Gamma>\<^sub>c  \<longrightarrow> 
                (\<exists>\<Sigma>'. \<Sigma>' \<in> com_step  S \<Sigma> \<Gamma>\<^sub>s \<and> 
                     (Normal \<sigma>',Normal \<Sigma>')\<in>\<gamma>\<^sub>n \<and> 
                     (Normal \<sigma>, Normal \<sigma>') \<in> G\<^sub>c \<and>
                     (Normal \<Sigma>, Normal \<Sigma>') \<in> G\<^sub>s)"
  sorry *)

lemma mod_sound:
  assumes  
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and
 a9:"C = Basic fc l \<or> C = Spec rc l \<or> C = Await bc Cc l" and 
 a9': "S = Basic fs l \<or> S = Spec rs l \<or> S = Await bs Cs l" and  
 a10:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<sigma>g' \<sigma>l' \<sigma>ls'  \<Sigma>g \<Sigma>l \<Sigma>ls  C'. 
       (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls))\<in>\<xi> \<and> (C',(\<sigma>g',\<sigma>l')) \<in> com_step  C (\<sigma>g,\<sigma>l)  \<Gamma>\<^sub>c  \<longrightarrow> 
         (\<exists>\<Sigma>g' \<Sigma>l' S'. (S', (\<Sigma>g',\<Sigma>l')) \<in> com_step  S (\<Sigma>g,\<Sigma>l) \<Gamma>\<^sub>s \<and> (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in>\<alpha> \<and> 
                  (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls)) \<in> G\<^sub>c \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s \<and>
                  ((C' = Skip  \<longrightarrow> (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in>\<gamma>\<^sub>n \<and> S' = Skip) \<and>
                  (C' = Throw  \<longrightarrow> (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in>\<gamma>\<^sub>a \<and> S' = Throw) \<and>
                  (C' = Stuck \<longrightarrow> S' = Stuck) \<and> (\<forall>f. C' = Fault f \<longrightarrow> S' = Fault f)))" and
 a11:"(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and
 a12:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v (C, (\<sigma>g,\<sigma>l)) \<rightarrow> (C', (\<sigma>g',\<sigma>l'))"
shows "\<exists>S' \<Sigma>g' \<Sigma>l'.
          (\<exists>S1 \<Sigma>g1 \<Sigma>l1. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (S1, (\<Sigma>g1, \<Sigma>l1)) \<and>
                 (\<exists>S2 \<Sigma>g2 \<Sigma>l2. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (S1, (\<Sigma>g1, \<Sigma>l1)) \<rightarrow> (S2, (\<Sigma>g2, \<Sigma>l2)) \<and> 
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S2, (\<Sigma>g2, \<Sigma>l2)) \<rightarrow>\<^sub>\<tau>\<^sup>* (S',  (\<Sigma>g',\<Sigma>l')))) \<and>
           (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in>\<alpha> \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls)) \<in> G\<^sub>c \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s \<and>                         
          (\<Gamma>\<^sub>c,(C', ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S', ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
proof-  
  have v_l:"v = l" using a12 a9 label_step by fastforce   
  have c1:"C' = Skip \<or> C' = Throw \<or> C' = Stuck \<or> (\<exists>f. C' = Fault f)" using a9 stepc_elim_cases1(3,4,8)
  proof -
    have "\<forall>f z c x ca xa. \<not> f\<turnstile>\<^sub>c\<^sub>z (c::('a, 'd, 'b, 'e) LanguageCon.com, x) \<rightarrow> (ca, xa) \<or> f\<turnstile>\<^sub>c (c, x) \<rightarrow> (ca, xa)"
      by (metis stepce_stepc)
    then show ?thesis
      using a12 a9 basic_skip spec_skip await_skip
      by (metis stepce_stepc)
  qed
  moreover {
    assume c1:"C' = Skip"
    then have  s1:"(C',(\<sigma>g',\<sigma>l')) \<in> com_step  C (\<sigma>g,\<sigma>l) \<Gamma>\<^sub>c" using a9 a12       
      by  (fastforce elim: stepc_elim_cases1(5) stepc_elim_cases1(6)  stepc_elim_cases1(10))+                 
    obtain \<Sigma>g' \<Sigma>l' S' where cond: "(S',(\<Sigma>g',\<Sigma>l')) \<in> com_step  S (\<Sigma>g,\<Sigma>l) \<Gamma>\<^sub>s \<and>  
                        S'=Skip \<and> (((\<sigma>g',\<sigma>l'),\<sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in>\<gamma>\<^sub>n \<and> 
                       (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls)) \<in> G\<^sub>c \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s"
      using a10 a11 c1 s1 by blast
    have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (S, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Skip, (\<Sigma>g',\<Sigma>l'))" 
      using  cond a9'   v_l
      by (meson com_step_Basic com_step_Spec_r com_step_await)           
    then have ?thesis using a11 cond  a1 a2 Skip_sim[OF  a2 _ a4   a6  ] c1 cond   
      unfolding related_transitions_def by blast           
  }
  moreover 
  { assume c1:"C' = Throw"
    then obtain bc Cc where c:"C = Await bc Cc l"
      using a9 a12 
      by  (fastforce elim: stepc_elim_cases1(5) stepc_elim_cases1(6)  stepc_elim_cases1(9))
    then have sn1: "(\<sigma>g,\<sigma>l) \<in> bc \<and> \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc, Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Abrupt (\<sigma>g',\<sigma>l')"
      using c1 a12 by (fastforce elim: stepc_elim_cases1(10))
    moreover have  s1:"(Throw,  (\<sigma>g',\<sigma>l')) \<in> com_step  C (\<sigma>g,\<sigma>l) \<Gamma>\<^sub>c" using c calculation by auto          
    ultimately obtain S' \<Sigma>g'  \<Sigma>l' where cond: "(S', (\<Sigma>g',\<Sigma>l'))  \<in> com_step  S (\<Sigma>g,\<Sigma>l) \<Gamma>\<^sub>s \<and>                             
                                (((\<sigma>g',\<sigma>l'),\<sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in>\<gamma>\<^sub>a \<and> S' = Throw \<and>
                                (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls)) \<in> G\<^sub>c \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s"
       using a10 a11 c1 s1  by blast         
    then have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (S,  (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Throw,  (\<Sigma>g',\<Sigma>l'))" 
      using   a9' sn1  v_l by (meson com_step_Basic com_step_Spec_r com_step_await)         
    then have sim:"(\<Gamma>\<^sub>c,(C', ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Throw, ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
      using cond Throw_sim[OF  a2' _ a5  _ ] a6 sn1 c1 by blast
    then have ?thesis using a2' steps   a11  cond  a1 sn1
      unfolding related_transitions_def
      by fastforce
  }
  moreover 
  { assume c1:"C' = Stuck"
    then have  s1:"(C',(\<sigma>g',\<sigma>l')) \<in> com_step  C (\<sigma>g,\<sigma>l) \<Gamma>\<^sub>c" using a9 a12       
      by  (fastforce elim: stepc_elim_cases1(5) stepc_elim_cases1(6)  stepc_elim_cases1(10))+    
    obtain \<Sigma>g' \<Sigma>l' S' where cond: "(S',(\<Sigma>g',\<Sigma>l')) \<in> com_step  S (\<Sigma>g,\<Sigma>l) \<Gamma>\<^sub>s \<and> S'=Stuck \<and>  
                       (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in>\<alpha> \<and>
                       (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls)) \<in> G\<^sub>c \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s"
      using a10 a11 c1 s1 by blast
    then have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (S,  (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Stuck,  (\<Sigma>g',\<Sigma>l'))" 
      using   a9'  v_l by (meson com_step_Basic com_step_Spec_r com_step_await)         
    then have sim:"(\<Gamma>\<^sub>c,(C', ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Stuck, ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
      using cond Stuck_sim a1 a6  c1 cond by blast
    then have ?thesis using a2' steps   a11  cond  a1 
      unfolding related_transitions_def
      by fastforce
  }
  moreover 
  { fix f 
    assume c1:"C' = Fault f"
    then have  s1:"(C',(\<sigma>g',\<sigma>l')) \<in> com_step  C (\<sigma>g,\<sigma>l) \<Gamma>\<^sub>c" using a9 a12       
      by  (fastforce elim: stepc_elim_cases1(5) stepc_elim_cases1(6)  stepc_elim_cases1(10))+    
    obtain \<Sigma>g' \<Sigma>l' S' where cond: "(S',(\<Sigma>g',\<Sigma>l')) \<in> com_step  S (\<Sigma>g,\<Sigma>l) \<Gamma>\<^sub>s \<and> S'=Fault f \<and>  
                       (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in>\<alpha> \<and>
                       (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls)) \<in> G\<^sub>c \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s"
      using a10 a11 c1 s1 by blast
    then have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (S,  (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Fault f,  (\<Sigma>g',\<Sigma>l'))" 
      using   a9'  v_l by (meson com_step_Basic com_step_Spec_r com_step_await)         
    then have sim:"(\<Gamma>\<^sub>c,(C', ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Fault f, ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
      using cond Fault_sim a1 a6  c1 cond by auto
    then have ?thesis using a2' steps   a11  cond  a1 
      unfolding related_transitions_def
      by fastforce
  }
  ultimately show ?thesis by auto 
qed


lemma intro_tau_step:"(\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                 (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c1', s1'))) \<Longrightarrow>          
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, \<Sigma>) \<rightarrow>\<^sub>\<tau>\<^sup>* (c1', s1') "  
  by auto           
  

lemma state_mod_sim_not_normal: assumes 
     a1:"(\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                       (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>e (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (S', (\<Sigma>g',\<Sigma>l')))) \<and>               
                       (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<alpha> \<and>
                       (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s \<and> 
                       (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)) \<in> G\<^sub>c \<and>
                (\<Gamma>\<^sub>c,(c\<^sub>c', ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S', ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
   shows" \<exists>\<Sigma>g' \<Sigma>l'. 
             (\<exists>S'. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (S', (\<Sigma>g',\<Sigma>l')) \<or>
                      (\<exists>v. e = Some v \<and>
                           (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                                  (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                                           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (S', (\<Sigma>g',\<Sigma>l')))))) \<and> 
                      (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)) \<in> G\<^sub>c \<and>
                     (\<Gamma>\<^sub>c,(c\<^sub>c', ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S', ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s))"
proof-  
  have "(\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (S', (\<Sigma>g',\<Sigma>l')) \<or>
                      (\<exists>v. e = Some v \<and>
                           (\<exists>a b. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b) \<and>
                                  (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, b) \<rightarrow> (aa, ba) \<and>
                                           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (S', (\<Sigma>g',\<Sigma>l'))))))"
    using a1 by (cases e, fastforce+) 
  then show ?thesis using a1 by metis
qed



lemma mod_state_tau_sound: 
  assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c"  and 
 a9:"C = Basic fc v \<or> C = Spec rc v \<or>  C = Await bc Cc v" and 
 a9': "S = Basic fs v \<or> S = Spec rs v \<or> S = Await bs Cs v" and  
 a10:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<sigma>g' \<sigma>l' \<sigma>ls'  \<Sigma>g \<Sigma>l \<Sigma>ls  C'. 
       (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls))\<in>\<xi> \<and> (C',(\<sigma>g',\<sigma>l')) \<in> com_step  C (\<sigma>g,\<sigma>l)  \<Gamma>\<^sub>c  \<longrightarrow> 
         (\<exists>\<Sigma>g' \<Sigma>l' S'. (S', (\<Sigma>g',\<Sigma>l')) \<in> com_step  S (\<Sigma>g,\<Sigma>l) \<Gamma>\<^sub>s \<and> (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in>\<alpha> \<and> 
                  (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls)) \<in> G\<^sub>c \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s \<and>
                  ((C' = Skip  \<longrightarrow> (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in>\<gamma>\<^sub>n \<and> S' = Skip) \<and>
                  (C' = Throw  \<longrightarrow> (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in>\<gamma>\<^sub>a \<and> S' = Throw) \<and>
                  (C' = Stuck \<longrightarrow> S' = Stuck) \<and> (\<forall>f. C' = Fault f \<longrightarrow> S' = Fault f)))"
shows "(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)"  
proof-
{ fix \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls 
  assume a11: "(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>"    
  then have "(\<Gamma>\<^sub>c,(C,((\<sigma>g,\<sigma>l),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S,((\<Sigma>g,\<Sigma>l),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"  
    apply (coinduction arbitrary: \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls)
    apply clarsimp
    apply (rule conjId)+
    using a9 apply auto[4]         
       apply (blast dest: sim_env[OF _ a3 _])
      apply (rule, rule, rule, rule, rule )
    subgoal for \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls v C' \<sigma>g' \<sigma>l'
      apply (frule mod_sound[OF a1 a2 a2' a3 a4 a5 a6    a9 a9' a10]) 
      unfolding toSeq_def apply force        
      apply auto[1]
      apply (frule subsetD[OF a1])
      by (meson related_transition_intro)        
    using a10 apply auto[2] 
    subgoal for \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls c\<^sub>c' a b 
      apply(frule mod_sound[OF  a1 a2 a2' a3 a4 a5 a6   a9 a9' a10], auto)   
      unfolding toSeq_def apply auto[1]   
      apply (frule related_transition_intro[OF subsetD[OF a1]], assumption+)
      by (metis (no_types) fst_conv intro_tau_step)         
    using  a1  by auto   
  } then show ?thesis unfolding RGSim_pre_def by auto
qed

(* |"com_step Skip s \<Gamma> = {Normal s} "
|"com_step (Seq _ _) s \<Gamma> = {Normal s}"    
|"com_step (Cond _ _ _) s \<Gamma> = {Normal s}"
| "com_step (While _ _) s \<Gamma> = {Normal s}"
| "com_step (Call _) s \<Gamma> = {Normal s}" 
| "com_step (DynCom _) s \<Gamma> = {Normal s}" 
| "com_step (Guard _ _ _) s \<Gamma> = {Normal s}" 
| "com_step Throw s \<Gamma> = {Normal s}"
| "com_step (Catch _ _) s \<Gamma> = {Normal s}"  *)

(* primrec com_step1::"('s,'p,'f,'e) com \<Rightarrow> ('s,'p,'f,'e) body \<Rightarrow> 's set \<Rightarrow> 's set \<Rightarrow> ('s,'f) xstate"
  where                         
"com_step1 C (Normal s) \<Gamma> = com_step_n1 C s \<Gamma>"
|"com_step1 C (Abrupt s) \<Gamma> = {Abrupt s}"
|"com_step1 C Stuck \<Gamma> = {Stuck}"
|"com_step1 C (Fault f) \<Gamma> = {Fault f}" *)


lemma step_imp_normal_rel_:
  assumes 
 a0:"\<forall>\<sigma>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> (P \<sigma>n) Cc (Q \<sigma>n), s" and
 a1:"\<sigma> \<in> P \<sigma>" and
 a2:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Normal \<sigma>'"
shows
 "\<sigma>' \<in> Q \<sigma>"
proof-
 obtain n where " \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Cc,Normal \<sigma>\<rangle> =n\<Rightarrow> Normal \<sigma>'"
    using a2 Semantic.exec_to_execn by fastforce 
  moreover have "\<And>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<Turnstile>n:\<^bsub>/F\<^esub>  
        (P \<sigma>) Cc 
        (Q \<sigma>), s"
   using a0 a2   hoare_cnvalid by fastforce
  ultimately show ?thesis  unfolding cnvalid_def nvalid_def  
    using a2 a1  by blast
qed

lemma in_normal_not_abrupt:
  assumes 
 a0:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> P1 Cc Q, {}" and
  a1: "\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Abrupt \<sigma>'" and
   a3:"\<sigma> \<in> P1"
shows "P"
proof-
  obtain n where " \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Cc,Normal \<sigma>\<rangle> =n\<Rightarrow> Abrupt \<sigma>'"
    using a1 Semantic.exec_to_execn by fastforce 
  moreover have "\<And>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<Turnstile>n:\<^bsub>/F\<^esub> P1 Cc Q, {}"
    using a0  hoare_cnvalid by fastforce
  ultimately show ?thesis unfolding cnvalid_def nvalid_def using  a3 by fastforce
qed

lemma not_normal_false:
  assumes 
 a0:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> P1 Cc Q, {}" and
  a1: "\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow>  \<sigma>'" and a2:"\<forall>\<sigma>''. \<sigma>' \<noteq> Normal \<sigma>''" and
   a3:"\<sigma> \<in> P1" and a4:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Semantic.Fault f"
shows "P"
proof-
  obtain n where " \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Cc,Normal \<sigma>\<rangle> =n\<Rightarrow>  \<sigma>'"
    using a1 Semantic.exec_to_execn by fastforce 
  moreover have "\<And>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<Turnstile>n:\<^bsub>/F\<^esub> P1 Cc Q, {}"
    using a0  hoare_cnvalid by fastforce
  ultimately obtain \<sigma>'' where "\<sigma>' = Normal \<sigma>''" unfolding cnvalid_def nvalid_def using  a3 a4
    using a1 by blast 
  then show ?thesis unfolding cnvalid_def nvalid_def using  a2 by auto
qed

lemma not_normal_false1:
  assumes 
 a0:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> P1 Cc Q, {}" and
  a1: "\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow>  \<sigma>'" and a2:"\<forall>\<sigma>''. \<sigma>' \<noteq> Normal \<sigma>''" and
   a3:"\<sigma> \<in> P1" and a4:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Semantic.Fault f"
shows "P"
proof-
  obtain n where " \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Cc,Normal \<sigma>\<rangle> =n\<Rightarrow>  \<sigma>'"
    using a1 Semantic.exec_to_execn by fastforce 
  moreover have "\<And>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<Turnstile>n:\<^bsub>/F\<^esub> P1 Cc Q, {}"
    using a0  hoare_cnvalid by fastforce
  ultimately obtain \<sigma>'' where "\<sigma>' = Normal \<sigma>''" unfolding cnvalid_def nvalid_def using  a3 a4
    using a1 by blast 
  then show ?thesis unfolding cnvalid_def nvalid_def using  a2 by auto
qed


lemma step_spec_normal_rel:
  assumes 
 a0:"\<forall>\<sigma>g \<sigma>l \<sigma>ls. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> (bc \<inter> {s. (fst ((\<sigma>g,\<sigma>l),\<sigma>ls)) = s \<and> ((\<sigma>g,\<sigma>l),\<sigma>ls) \<in> Domain \<xi>}) Cc 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>n)}), 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>a)})" and
 a1:"\<forall>\<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls),  (s,\<Sigma>ls)) \<in> \<xi> } \<inter> bs \<inter> {fst((\<Sigma>g,\<Sigma>l),\<Sigma>ls)}) Cs 
         ({s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (s,\<Sigma>ls)) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>n',\<Sigma>ls))\<in> \<gamma>\<^sub>n}), {}" and 
 a2:"(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and a3:"(\<sigma>g,\<sigma>l) \<in> bc" and a4:"(\<Sigma>g,\<Sigma>l)\<in>bs" and
 a5:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Normal (\<sigma>g',\<sigma>l')" and 
 a6:"\<forall>\<Sigma>g \<Sigma>l. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal (\<Sigma>g,\<Sigma>l)\<rangle> \<Rightarrow> Semantic.Fault f"
shows "\<exists>\<Sigma>'. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal (\<Sigma>g,\<Sigma>l)\<rangle> \<Rightarrow> Normal \<Sigma>' \<and> (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>',\<Sigma>ls))\<in>\<gamma>\<^sub>n \<and>
       (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (\<Sigma>',\<Sigma>ls))\<in>G\<^sub>s"
proof-
  obtain n where " \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> =n\<Rightarrow> Normal (\<sigma>g',\<sigma>l')"
    using a5 Semantic.exec_to_execn by fastforce 
  moreover have "\<And>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<Turnstile>n:\<^bsub>/F\<^esub>  
         (bc \<inter> {s. (fst ((\<sigma>g,\<sigma>l),\<sigma>ls)) = s \<and> ((\<sigma>g,\<sigma>l),\<sigma>ls) \<in> Domain \<xi>}) Cc 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>n)}), 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>a)})"
   using a0 a2 a3 hoare_cnvalid by fastforce
  ultimately have "((\<sigma>g',\<sigma>l'),\<sigma>ls) \<in> Domain \<gamma>\<^sub>n"  unfolding cnvalid_def nvalid_def  
    using a2 a3  by fastforce
  have " \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls),  (s,\<Sigma>ls)) \<in> \<xi> } \<inter> bs \<inter> {fst((\<Sigma>g,\<Sigma>l),\<Sigma>ls)}) Cs 
         ({s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (s,\<Sigma>ls)) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>n',\<Sigma>ls))\<in> \<gamma>\<^sub>n}), {}"
    using a2 a1 by blast
  then have "\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> 
        ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls),  (s,\<Sigma>ls)) \<in> \<xi> } \<inter> bs \<inter> {fst((\<Sigma>g,\<Sigma>l),\<Sigma>ls)}) Cs 
         ({s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (s,\<Sigma>ls)) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>n',\<Sigma>ls))\<in> \<gamma>\<^sub>n}), {}"
    using hoaret_sound' by blast  
  thus ?thesis  
    using a4 a2 a6 Termination.terminates_implies_exec   unfolding validt_def valid_def
    by fastforce
qed

lemma step_spec_abrupt_rel:
  assumes 
 a0:"\<forall>\<sigma>g \<sigma>l \<sigma>ls. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> (bc \<inter> {s. (fst ((\<sigma>g,\<sigma>l),\<sigma>ls)) = s \<and> ((\<sigma>g,\<sigma>l),\<sigma>ls) \<in> Domain \<xi>}) Cc 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>n)}), 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>a)})" and
 a1:"\<forall>\<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls),  (s,\<Sigma>ls)) \<in> \<xi> } \<inter> bs \<inter> {fst((\<Sigma>g,\<Sigma>l),\<Sigma>ls)}) Cs 
         {},({s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (s,\<Sigma>ls)) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>n',\<Sigma>ls))\<in> \<gamma>\<^sub>a})" and
 a2:"(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and a3:"(\<sigma>g,\<sigma>l) \<in> bc" and a4:"(\<Sigma>g,\<Sigma>l)\<in>bs" and
 a5:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> (Semantic.Abrupt (\<sigma>g',\<sigma>l'))" and 
 a6:"\<forall>\<Sigma>g \<Sigma>l. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal (\<Sigma>g,\<Sigma>l)\<rangle> \<Rightarrow> Semantic.Fault f"
shows "\<exists>\<Sigma>'. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal (\<Sigma>g,\<Sigma>l)\<rangle> \<Rightarrow> Semantic.Abrupt \<Sigma>' \<and> (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>',\<Sigma>ls))\<in>\<gamma>\<^sub>a \<and> 
           ( ((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (\<Sigma>',\<Sigma>ls))\<in>G\<^sub>s"
proof-
 obtain n where " \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> =n\<Rightarrow> Semantic.Abrupt (\<sigma>g',\<sigma>l')"
    using a5 Semantic.exec_to_execn by fastforce 
  moreover have "\<And>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<Turnstile>n:\<^bsub>/F\<^esub>  
         (bc \<inter> {s. (fst ((\<sigma>g,\<sigma>l),\<sigma>ls)) = s \<and> ((\<sigma>g,\<sigma>l),\<sigma>ls) \<in> Domain \<xi>}) Cc 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>n)}), 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>a)})"
   using a0 a2 a3 hoare_cnvalid by fastforce
  ultimately have "((\<sigma>g',\<sigma>l'),\<sigma>ls) \<in> Domain \<gamma>\<^sub>a"  unfolding cnvalid_def nvalid_def  
    using a2 a3 a5 by fastforce
  have "\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls),  (s,\<Sigma>ls)) \<in> \<xi> } \<inter> bs \<inter> {fst((\<Sigma>g,\<Sigma>l),\<Sigma>ls)}) Cs 
         {}, ({s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (s,\<Sigma>ls)) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>n',\<Sigma>ls))\<in> \<gamma>\<^sub>a})"
    using a2 a1 by blast
  then have "\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls),  (s,\<Sigma>ls)) \<in> \<xi> } \<inter> bs \<inter> {fst((\<Sigma>g,\<Sigma>l),\<Sigma>ls)}) Cs 
         {}, ({s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (s,\<Sigma>ls)) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>n',\<Sigma>ls))\<in> \<gamma>\<^sub>a})"
    using hoaret_sound' by blast  
  thus ?thesis  
    using a4 a2 a6 Termination.terminates_implies_exec  unfolding validt_def valid_def
    by fastforce
qed

lemma step_imp_normal_rel:
  assumes 
 a0:"\<forall>\<sigma>g \<sigma>l \<sigma>ls. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. (fst ((\<sigma>g,\<sigma>l),\<sigma>ls)) = s \<and> ((\<sigma>g,\<sigma>l),\<sigma>ls) \<in> Domain \<xi>}) Cc 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>n)}), 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>a)})" and
 a1:"(\<sigma>g,\<sigma>l) \<in>bc \<and> ((\<sigma>g,\<sigma>l),\<sigma>ls) \<in>Domain \<xi>" and
 a2:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Normal (\<sigma>g',\<sigma>l')"
shows
 "((\<sigma>g',\<sigma>l'),\<sigma>ls)\<in> Domain \<gamma>\<^sub>n \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls))\<in> G\<^sub>c"
proof-
 obtain n where " \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> =n\<Rightarrow> Normal (\<sigma>g',\<sigma>l')"
    using a2 Semantic.exec_to_execn by fastforce 
  moreover have "\<And>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<Turnstile>n:\<^bsub>/F\<^esub>  
         (bc \<inter> {s. (fst ((\<sigma>g,\<sigma>l),\<sigma>ls)) = s \<and> ((\<sigma>g,\<sigma>l),\<sigma>ls) \<in> Domain \<xi>}) Cc 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>n)}), 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>a)})"
   using a0 a2   hoare_cnvalid by fastforce
  ultimately show ?thesis  unfolding cnvalid_def nvalid_def  
    using a2 a1  by fastforce
qed

lemma step_imp_normal_rel1:
  assumes 
 a0:"\<forall>\<sigma>g \<sigma>l \<sigma>ls. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. (fst ((\<sigma>g,\<sigma>l),\<sigma>ls)) = s \<and> ((\<sigma>g,\<sigma>l),\<sigma>ls) \<in> Domain \<xi>}) Cc 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> p}), s" and
 a1:"(\<sigma>g,\<sigma>l) \<in>bc \<and> ((\<sigma>g,\<sigma>l),\<sigma>ls) \<in>Domain \<xi>" and
 a2:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Normal (\<sigma>g',\<sigma>l')"
shows
 "((\<sigma>g',\<sigma>l'),\<sigma>ls) \<in> p \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls))\<in> G\<^sub>c"
proof-
 obtain n where " \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> =n\<Rightarrow> Normal (\<sigma>g',\<sigma>l')"
    using a2 Semantic.exec_to_execn by fastforce 
  moreover have "\<And>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<Turnstile>n:\<^bsub>/F\<^esub>  
        (bc \<inter> {s. (fst ((\<sigma>g,\<sigma>l),\<sigma>ls)) = s \<and> ((\<sigma>g,\<sigma>l),\<sigma>ls) \<in> Domain \<xi>}) Cc 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> p}), s"
   using a0 a2   hoare_cnvalid by fastforce
  ultimately show ?thesis  unfolding cnvalid_def nvalid_def  
    using a2 a1  by fastforce
qed

lemma step_imp_normal_rel2:
  assumes 
 a0:"\<forall>\<sigma>g \<sigma>l \<sigma>ls. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. (fst ((\<sigma>g,\<sigma>l),\<sigma>ls)) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Cc        
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> s \<in> p}), s" and
 a1:"(\<sigma>g,\<sigma>l) \<in>bc \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and
 a2:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Normal (\<sigma>g',\<sigma>l')"
shows
 "(\<sigma>g',\<sigma>l') \<in> p \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls))\<in> G\<^sub>c"
proof-
 obtain n where  " \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> =n\<Rightarrow> Normal (\<sigma>g',\<sigma>l')"
    using a2 Semantic.exec_to_execn by fastforce 
  moreover have "\<And>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<Turnstile>n:\<^bsub>/F\<^esub>  
        (bc \<inter> {s. (fst ((\<sigma>g,\<sigma>l),\<sigma>ls)) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Cc        
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> s \<in> p}), s"
   using a0 a2   hoare_cnvalid by fastforce
  ultimately show ?thesis  unfolding cnvalid_def nvalid_def  
    using a2 a1  by fastforce
qed


lemma step_imp_normal_rel3:
  assumes 
 a0:"\<forall>\<sigma>g \<sigma>l. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. (fst ((\<sigma>g,\<sigma>l),\<sigma>ls)) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Cc        
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c} \<inter> p), s" and
 a1:"(\<sigma>g,\<sigma>l) \<in>bc \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and
 a2:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Normal (\<sigma>g',\<sigma>l')"
shows
 "(\<sigma>g',\<sigma>l') \<in> p \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls))\<in> G\<^sub>c"
proof-
 obtain n where  " \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> =n\<Rightarrow> Normal (\<sigma>g',\<sigma>l')"
    using a2 Semantic.exec_to_execn by fastforce 
  moreover have "\<And>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<Turnstile>n:\<^bsub>/F\<^esub>  
        (bc \<inter> {s. (fst ((\<sigma>g,\<sigma>l),\<sigma>ls)) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Cc        
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c} \<inter>  p), s"
   using a0 a2   hoare_cnvalid by fastforce
  ultimately show ?thesis  unfolding cnvalid_def nvalid_def  
    using a2 a1  by fastforce
qed

lemma step_imp_abrupt_rel:
  assumes 
 a0:"\<forall>\<sigma>g \<sigma>l \<sigma>ls. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. (fst ((\<sigma>g,\<sigma>l),\<sigma>ls)) = s \<and> ((\<sigma>g,\<sigma>l),\<sigma>ls) \<in> Domain \<xi>}) Cc 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>n)}), 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>a)})" and
 a1:"(\<sigma>g,\<sigma>l) \<in>bc \<and> ((\<sigma>g,\<sigma>l),\<sigma>ls) \<in>Domain \<xi>" and
 a2:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Abrupt (\<sigma>g',\<sigma>l')"
shows
 "((\<sigma>g',\<sigma>l'),\<sigma>ls)\<in> Domain \<gamma>\<^sub>a \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls))\<in> G\<^sub>c"
proof-
 obtain n where " \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Cc,Normal(\<sigma>g,\<sigma>l)\<rangle> =n\<Rightarrow> Abrupt (\<sigma>g',\<sigma>l')"
    using a2 Semantic.exec_to_execn by fastforce 
  moreover have "\<And>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<Turnstile>n:\<^bsub>/F\<^esub>  
         (bc \<inter> {s. (fst ((\<sigma>g,\<sigma>l),\<sigma>ls)) = s \<and> ((\<sigma>g,\<sigma>l),\<sigma>ls) \<in> Domain \<xi>}) Cc 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>n)}), 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>a)})"
   using a0 a2   hoare_cnvalid by fastforce
  ultimately show ?thesis  unfolding cnvalid_def nvalid_def  
    using a2 a1  by fastforce
qed


lemma await_sim':assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and 
 a9:"C = Await bc Cc v" and 
 a9': "S = Await bs Cs v" and  
a10:"\<forall>\<sigma>g \<sigma>l \<sigma>ls. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> (bc \<inter> {s. (fst ((\<sigma>g,\<sigma>l),\<sigma>ls)) = s \<and> ((\<sigma>g,\<sigma>l),\<sigma>ls) \<in> Domain \<xi>}) Cc 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>n)}), 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>a)})" and
 a11a:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<sigma>g' \<sigma>l'. ((\<sigma>g, \<sigma>l), \<sigma>ls) \<in> Domain \<xi> \<and> (\<sigma>g, \<sigma>l) \<in> bc \<and> 
                          \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a \<turnstile>\<langle>Cc,Normal (\<sigma>g, \<sigma>l)\<rangle> \<Rightarrow> Normal (\<sigma>g', \<sigma>l') \<longrightarrow>  
       (\<forall>\<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
          ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls),  (s,\<Sigma>ls)) \<in> \<xi> } \<inter> bs \<inter> {fst((\<Sigma>g,\<Sigma>l),\<Sigma>ls)}) Cs 
         ({s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (s,\<Sigma>ls)) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>n',\<Sigma>ls))\<in> \<gamma>\<^sub>n}), {})" and 
a11b:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<sigma>g' \<sigma>l'. ((\<sigma>g, \<sigma>l), \<sigma>ls) \<in> Domain \<xi> \<and> (\<sigma>g, \<sigma>l) \<in> bc \<and> 
                          \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a \<turnstile>\<langle>Cc,Normal (\<sigma>g, \<sigma>l)\<rangle> \<Rightarrow> Abrupt (\<sigma>g', \<sigma>l') \<longrightarrow>   
       (\<forall>\<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls),  (s,\<Sigma>ls)) \<in> \<xi> } \<inter> bs \<inter> {fst((\<Sigma>g,\<Sigma>l),\<Sigma>ls)}) Cs 
         {},({s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (s,\<Sigma>ls)) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>n',\<Sigma>ls))\<in> \<gamma>\<^sub>a}) )" and 
 a12: "(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi> " and
 a13: "\<xi> \<subseteq> \<up>(bc \<rightleftharpoons> bs)" and
 a14:"\<forall>\<Sigma>g \<Sigma>l. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal (\<Sigma>g, \<Sigma>l)\<rangle> \<Rightarrow> Semantic.Fault f" and 
a15: "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (C, (\<sigma>g,\<sigma>l)) \<rightarrow> (c1,  (\<sigma>g',\<sigma>l'))" and a16:"c1 = Skip \<or> c1 = Throw"
shows "\<exists>c1' \<Sigma>g' \<Sigma>l'. 
         (\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S,  (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
         (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c1',  (\<Sigma>g',\<Sigma>l')))) \<and>
         (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<alpha> \<and>
         (((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls)), (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
        (\<Gamma>\<^sub>c,(c1, ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1', ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
proof-
  have v_eq:"v1 = v" using a15 a9
    using label_step by fastforce
  have a12': "((\<sigma>g,\<sigma>l),\<sigma>ls)\<in>Domain \<xi>" using a12 by auto  
  then have a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (Await bc Cc v1, (\<sigma>g,\<sigma>l)) \<rightarrow> (c1,(\<sigma>g',\<sigma>l'))" using a15 a9  v_eq by auto     
  show ?thesis using a16
  proof
    assume a001:"c1 = Skip"
    then have \<sigma>b:"(\<sigma>g,\<sigma>l)\<in>bc" and step:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Normal (\<sigma>g',\<sigma>l')" 
      using stepc_elim_cases1(10)[OF a00]
      by (fast+)
    then have "\<forall>\<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
        ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls),  (s,\<Sigma>ls)) \<in> \<xi> } \<inter> bs \<inter> {fst((\<Sigma>g,\<Sigma>l),\<Sigma>ls)}) Cs 
       ({s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (s,\<Sigma>ls)) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>n',\<Sigma>ls))\<in> \<gamma>\<^sub>n}), {}"
      using a11a a12' by auto
    have \<Sigma>b:"(\<Sigma>g,\<Sigma>l)\<in>bs"  using \<sigma>b a12 a13 same_set by fastforce
    then obtain  \<Sigma>g' \<Sigma>l' where 
      step_cs:"\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal (\<Sigma>g,\<Sigma>l)\<rangle> \<Rightarrow> Normal (\<Sigma>g',\<Sigma>l') \<and> 
               (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)) \<in> \<gamma>\<^sub>n \<and> 
               (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls))\<in>G\<^sub>s"
      using step_spec_normal_rel[OF a10 _ a12 \<sigma>b _ step a14, of bs G\<^sub>s] a11a a12' step \<sigma>b
      by auto
    moreover have " (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls))\<in> G\<^sub>c" 
      using step_imp_normal_rel[OF a10 conjI[OF \<sigma>b a12'] step]
      by auto
    then have "((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)), (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>" 
      using calculation(1) a1 a12 a2 unfolding related_transitions_def by fastforce
    moreover have "\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
                        (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, (\<Sigma>g',\<Sigma>l')))"
      using calculation(1) \<Sigma>b a9' Awaitc[OF \<Sigma>b _] v_eq by fastforce   
    moreover have "(\<Gamma>\<^sub>c,(Skip, ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Skip,((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
      using Skip_sim[OF a2 _ a4 a6  ] step_cs by blast
    ultimately show ?thesis using a1 a12 a2 a9 a9' a001 by blast
  next    
    assume a001:"c1 = Throw"
     then have \<sigma>b:"(\<sigma>g,\<sigma>l)\<in>bc" and step:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Abrupt (\<sigma>g',\<sigma>l')" 
      using stepc_elim_cases1(10)[OF a00]
      by (fast+)           
    then have "\<forall>\<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
        ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls),  (s,\<Sigma>ls)) \<in> \<xi> } \<inter> bs \<inter> {fst((\<Sigma>g,\<Sigma>l),\<Sigma>ls)}) Cs 
      {}, ({s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (s,\<Sigma>ls)) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>n',\<Sigma>ls))\<in> \<gamma>\<^sub>a})"
      using a11b a12' by auto
    have \<Sigma>b:"(\<Sigma>g,\<Sigma>l)\<in>bs"  using \<sigma>b a12 a13 same_set by fastforce
    then obtain \<Sigma>g' \<Sigma>l' where 
     step_cs:"\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal (\<Sigma>g,\<Sigma>l)\<rangle> \<Rightarrow> Abrupt (\<Sigma>g',\<Sigma>l') \<and> 
               (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)) \<in> \<gamma>\<^sub>a \<and> 
               (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls))\<in>G\<^sub>s"
      using step_spec_abrupt_rel[OF a10 _ a12 \<sigma>b _ step a14, of bs G\<^sub>s] a11b a12' step \<sigma>b
      by auto
    moreover have " (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls))\<in> G\<^sub>c"  
      using step_imp_abrupt_rel[OF a10 conjI[OF \<sigma>b a12'] step]
      by auto
    then have "((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)), (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>" 
      using calculation(1) a1 a12 a2' unfolding related_transitions_def by fastforce
    moreover have "\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S,(\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
                        (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw,(\<Sigma>g',\<Sigma>l')))"
      using calculation(1) \<Sigma>b a9' AwaitAbruptc[OF \<Sigma>b _] v_eq by fastforce      
    moreover have "(\<Gamma>\<^sub>c,(Throw,  ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Throw,((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
      using Throw_sim[OF a2' _ a5 _  ] a6 step_cs by blast
    ultimately show ?thesis using a1 a12 a2' a9 a9' a001 by blast       
  qed
qed

lemma Step_Await_not_normal: 
  assumes a0:
     "\<forall>\<sigma>g \<sigma>l \<sigma>ls. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> (bc \<inter> {s. (fst ((\<sigma>g,\<sigma>l),\<sigma>ls)) = s \<and> ((\<sigma>g,\<sigma>l),\<sigma>ls) \<in> Domain \<xi>}) Cc 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>n)}), 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>a)})" and 
      a1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (Await bc Cc v, (\<sigma>g,\<sigma>l)) \<rightarrow> (c\<^sub>c', (\<sigma>g',\<sigma>l'))" and
      a2:"c\<^sub>c' = Stuck \<or> (\<exists>f. c\<^sub>c' = Fault f)" and a3:"(((\<sigma>g,\<sigma>l),\<sigma>ls),  ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and  
      a03:"\<forall>\<sigma>g \<sigma>l. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal  (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Semantic.Fault f"
    shows "P"
proof-  
  obtain \<sigma>n where 
    bn:"(\<sigma>g,\<sigma>l)\<in>bc \<and> \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> \<sigma>n \<and> (\<forall>t'. \<sigma>n \<noteq> Semantic.Abrupt t' \<and> \<sigma>n \<noteq> Normal t')" 
    using   a2
    by (metis LocalRG_HoareDef.stepc_elim_cases_Await_Fault a1 stepc_elim_cases_Await_Stuck 
            stepce_stepc xstate.simps(11) xstate.simps(13) xstate.simps(7) xstate.simps(9))
  moreover have a0:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> (bc \<inter> {s. (fst ((\<sigma>g,\<sigma>l),\<sigma>ls)) = s \<and> ((\<sigma>g,\<sigma>l),\<sigma>ls) \<in> Domain \<xi>}) Cc 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>n)}), 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>a)})"
    using a3 a0 by auto  
  obtain n where  step:" \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile> \<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> =n\<Rightarrow>  \<sigma>n"
    using a0 bn Semantic.exec_to_execn by fastforce 
  moreover have val:"\<And>n. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<Turnstile>n:\<^bsub>/F\<^esub> (bc \<inter> {s. (fst ((\<sigma>g,\<sigma>l),\<sigma>ls)) = s \<and> ((\<sigma>g,\<sigma>l),\<sigma>ls) \<in> Domain \<xi>}) Cc 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>n)}), 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>a)})"
    using a0 a2 a3 hoare_cnvalid by fastforce
  have   
   "\<exists>\<sigma>n'. \<sigma>n = Abrupt \<sigma>n' \<or> \<sigma>n = Normal \<sigma>n'" 
    using a2 val bn a3 step a03 unfolding cnvalid_def nvalid_def
    by (cases \<sigma>n, fastforce+)    
  thus ?thesis  using bn  by auto 
qed


lemma await_sim:assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and 
 a9:"C = Await bc Cc v" and 
 a9': "S = Await bs Cs v" and  
a10:"\<forall>\<sigma>g \<sigma>l \<sigma>ls. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> (bc \<inter> {s. (fst ((\<sigma>g,\<sigma>l),\<sigma>ls)) = s \<and> ((\<sigma>g,\<sigma>l),\<sigma>ls) \<in> Domain \<xi>}) Cc 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>n)}), 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>a)})" and
 a11a:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<sigma>g' \<sigma>l'. ((\<sigma>g, \<sigma>l), \<sigma>ls) \<in> Domain \<xi> \<and> (\<sigma>g, \<sigma>l) \<in> bc \<and> 
                          \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a \<turnstile>\<langle>Cc,Normal (\<sigma>g, \<sigma>l)\<rangle> \<Rightarrow> Normal (\<sigma>g', \<sigma>l') \<longrightarrow>  
       (\<forall>\<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
          ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls),  (s,\<Sigma>ls)) \<in> \<xi> } \<inter> bs \<inter> {fst((\<Sigma>g,\<Sigma>l),\<Sigma>ls)}) Cs 
         ({s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (s,\<Sigma>ls)) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>n',\<Sigma>ls))\<in> \<gamma>\<^sub>n}), {})" and 
a11b:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<sigma>g' \<sigma>l'. ((\<sigma>g, \<sigma>l), \<sigma>ls) \<in> Domain \<xi> \<and> (\<sigma>g, \<sigma>l) \<in> bc \<and> 
                          \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a \<turnstile>\<langle>Cc,Normal (\<sigma>g, \<sigma>l)\<rangle> \<Rightarrow> Abrupt (\<sigma>g', \<sigma>l') \<longrightarrow>   
       (\<forall>\<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls),  (s,\<Sigma>ls)) \<in> \<xi> } \<inter> bs \<inter> {fst((\<Sigma>g,\<Sigma>l),\<Sigma>ls)}) Cs 
         {},({s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (s,\<Sigma>ls)) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>n',\<Sigma>ls))\<in> \<gamma>\<^sub>a}) )" and 
 a12: "(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi> " and
 a13: "\<xi> \<subseteq> \<up>(bc \<rightleftharpoons> bs)" and
 a14:"\<forall>\<Sigma>g \<Sigma>l. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal (\<Sigma>g, \<Sigma>l)\<rangle> \<Rightarrow> Semantic.Fault f" and 
a14':"\<forall>\<sigma>g \<sigma>l. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal  (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Semantic.Fault f" and
a15: "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (C, (\<sigma>g,\<sigma>l)) \<rightarrow> (c1,  (\<sigma>g',\<sigma>l'))" 
shows "\<exists>c1' \<Sigma>g' \<Sigma>l'. 
         (\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S,  (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
         (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c1',  (\<Sigma>g',\<Sigma>l')))) \<and>
         (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<alpha> \<and>
         (((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls)), (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
        (\<Gamma>\<^sub>c,(c1, ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1', ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
proof-
  have c1:"c1 = Skip \<or> c1 = Throw \<or> c1 = Stuck \<or> (\<exists>f. c1 = Fault f)"
    using stepc_elim_cases1(10)[OF a15[simplified a9]] by fastforce
  thus ?thesis 
  proof(cases "c1 = Skip \<or> c1 = Throw")
    case True then show ?thesis 
      using await_sim'[OF a1 a2 a2' a3 a4 a5 a6 a9 a9' a10 a11a a11b a12 a13 a14 a15]
      by auto
  next
    case False then have c1:"c1 = Stuck \<or> (\<exists>f. c1 = Fault f)" using c1 by auto
    then show ?thesis using Step_Await_not_normal[OF a10 a15[simplified a9] c1 a12 a14'] by auto
  qed
qed

lemma mod_state_Await_sound: 
  assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and 
a9:"C = Await bc Cc v" and 
 a9': "S = Await bs Cs v" and  
a10:"\<forall>\<sigma>g \<sigma>l \<sigma>ls. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> (bc \<inter> {s. (fst ((\<sigma>g,\<sigma>l),\<sigma>ls)) = s \<and> ((\<sigma>g,\<sigma>l),\<sigma>ls) \<in> Domain \<xi>}) Cc 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>n)}), 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s,\<sigma>ls)) \<in> G\<^sub>c \<and> (s,\<sigma>ls) \<in> (Domain \<gamma>\<^sub>a)})" and
 a11a:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<sigma>g' \<sigma>l'. ((\<sigma>g, \<sigma>l), \<sigma>ls) \<in> Domain \<xi> \<and> (\<sigma>g, \<sigma>l) \<in> bc \<and> 
                          \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a \<turnstile>\<langle>Cc,Normal (\<sigma>g, \<sigma>l)\<rangle> \<Rightarrow> Normal (\<sigma>g', \<sigma>l') \<longrightarrow>  
       (\<forall>\<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
          ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls),  (s,\<Sigma>ls)) \<in> \<xi> } \<inter> bs \<inter> {fst((\<Sigma>g,\<Sigma>l),\<Sigma>ls)}) Cs 
         ({s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (s,\<Sigma>ls)) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>n',\<Sigma>ls))\<in> \<gamma>\<^sub>n}), {})" and 
a11b:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<sigma>g' \<sigma>l'. ((\<sigma>g, \<sigma>l), \<sigma>ls) \<in> Domain \<xi> \<and> (\<sigma>g, \<sigma>l) \<in> bc \<and> 
                          \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a \<turnstile>\<langle>Cc,Normal (\<sigma>g, \<sigma>l)\<rangle> \<Rightarrow> Abrupt (\<sigma>g', \<sigma>l') \<longrightarrow>   
       (\<forall>\<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls),  (s,\<Sigma>ls)) \<in> \<xi> } \<inter> bs \<inter> {fst((\<Sigma>g,\<Sigma>l),\<Sigma>ls)}) Cs 
         {},({s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (s,\<Sigma>ls)) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>n',\<Sigma>ls))\<in> \<gamma>\<^sub>a}) )" and   
a13: "\<xi> \<subseteq> \<up>(bc \<rightleftharpoons> bs)" and
a14:"\<forall>\<Sigma>g \<Sigma>l. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal (\<Sigma>g, \<Sigma>l)\<rangle> \<Rightarrow> Semantic.Fault f" and  
a03:"\<forall>\<sigma>g \<sigma>l. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal  (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Semantic.Fault f"
shows "(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)"    
proof-
  {fix \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls
    assume a11: "(((\<sigma>g,\<sigma>l), \<sigma>ls), ((\<Sigma>g,\<Sigma>l), \<Sigma>ls)) \<in> \<xi>"   
    then have "(\<Gamma>\<^sub>c,(C,((\<sigma>g,\<sigma>l), \<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S,((\<Sigma>g,\<Sigma>l), \<Sigma>ls)),R\<^sub>s,G\<^sub>s)" 
     apply (coinduction arbitrary:  \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls)
      
      apply clarsimp
      apply (rule conjId)+ 
             apply (auto simp add: a9)
      using a3 env apply blast unfolding toSeq_def
        apply (frule await_sim[OF a1 a2 a2' a3 a4 a5 a6 a9 a9' a10 a11a a11b _ a13 a14 a03, simplified a9 toSeq_def])
      apply fastforce+         
       apply (frule await_sim[OF a1 a2 a2' a3 a4 a5 a6   a9 a9' a10 a11a a11b _ a13 a14 a03, simplified a9])
      apply fastforce 
      using intro_tau_step apply fastforce
      using a1 by auto
  }  then show ?thesis unfolding RGSim_pre_def  by auto
qed 

lemma basic_await_sim:assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and  
  a9:"C = Basic fc v" and 
 a9': "S = Await bs Cs v" and  
 a11:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<sigma>g' \<sigma>l' \<Sigma>g \<Sigma>l \<Sigma>ls. (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls))\<in>\<xi> \<and> 
       (Skip,  (\<sigma>g',\<sigma>l')) \<in> com_step  C (\<sigma>g,\<sigma>l)  \<Gamma>\<^sub>c \<longrightarrow>  
       (\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls),  (s,\<Sigma>ls)) \<in> \<xi> } \<inter> bs \<inter> {fst((\<Sigma>g,\<Sigma>l),\<Sigma>ls)}) Cs 
         ({s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (s,\<Sigma>ls)) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>n',\<Sigma>ls))\<in> \<gamma>\<^sub>n}), {})" and 
 a12: "(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi> " and  a13:"Range \<xi> \<subseteq> {s. fst s \<in> bs}" and 
a14:"\<forall>\<Sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal \<Sigma>\<rangle> \<Rightarrow> Semantic.Fault f" and 
a15: "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (C, (\<sigma>g,\<sigma>l)) \<rightarrow> (c1, (\<sigma>g',\<sigma>l'))" and
a16:"(((\<sigma>g,\<sigma>l),\<sigma>ls),  ((fc (\<sigma>g,\<sigma>l)), \<sigma>ls))\<in>G\<^sub>c" 
shows "\<exists>c1' \<Sigma>g' \<Sigma>l'. 
         (\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S,  (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
         (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c1',  (\<Sigma>g',\<Sigma>l')))) \<and>
         (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<alpha> \<and>
         (((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls)), (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
        (\<Gamma>\<^sub>c,(c1, ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1', ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
proof-
  have v_eq:"v1 = v" using a15 a9
    using label_step by fastforce
  have a12': "((\<sigma>g,\<sigma>l),\<sigma>ls)\<in>Domain \<xi>" using a12 by auto
  have \<Sigma>inbs: "(\<Sigma>g,\<Sigma>l)\<in>bs" using a13 a12 by auto
  then have a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (Basic fc v, (\<sigma>g,\<sigma>l)) \<rightarrow> (c1,  (\<sigma>g',\<sigma>l'))" using a15 a9  v_eq by auto
  then have c1:"c1 = Skip" and \<sigma>:"(\<sigma>g',\<sigma>l') = fc (\<sigma>g,\<sigma>l)" thm stepc_elim_cases
    by  (auto elim: stepc_elim_cases1)   
  then have " (Skip, (\<sigma>g',\<sigma>l')) \<in> com_step  C  (\<sigma>g,\<sigma>l)  \<Gamma>\<^sub>c" using a9 by auto
  then have " \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls),  (s,\<Sigma>ls)) \<in> \<xi> } \<inter> bs \<inter> {fst((\<Sigma>g,\<Sigma>l),\<Sigma>ls)}) Cs 
         ({s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (s,\<Sigma>ls)) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>n',\<Sigma>ls))\<in> \<gamma>\<^sub>n}), {}"
    using a12 a11 by blast
  then have "\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls),  (s,\<Sigma>ls)) \<in> \<xi> } \<inter> bs \<inter> {fst((\<Sigma>g,\<Sigma>l),\<Sigma>ls)}) Cs 
         ({s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (s,\<Sigma>ls)) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>n',\<Sigma>ls))\<in> \<gamma>\<^sub>n}), {}"
    using hoaret_sound' by blast  
  moreover have \<Sigma>b:"(\<Sigma>g,\<Sigma>l)\<in>bs"  using  a12 a13 by fastforce
  ultimately  obtain \<Sigma>g' \<Sigma>l' where 
    step_cs: "\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal (\<Sigma>g,\<Sigma>l)\<rangle> \<Rightarrow> Normal (\<Sigma>g',\<Sigma>l') \<and> 
      (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)) \<in> \<gamma>\<^sub>n \<and> 
       (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls))\<in>G\<^sub>s"
    using a12 a14 Termination.terminates_implies_exec[of "\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a" Cs "Normal (\<Sigma>g,\<Sigma>l)"]  unfolding validt_def valid_def    
    by fastforce
  then obtain \<Sigma>g' \<Sigma>l' where 
    step_cs: " \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal (\<Sigma>g,\<Sigma>l)\<rangle> \<Rightarrow> Normal (\<Sigma>g',\<Sigma>l') \<and> 
            (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)) \<in> \<gamma>\<^sub>n \<and> 
            (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls))\<in>G\<^sub>s" by auto
  moreover have " (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls))\<in> G\<^sub>c" using a16 \<sigma>
      by auto
  then have "((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls)), (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>" 
      using calculation(1) a1 a12 a2 unfolding related_transitions_def by fastforce
    moreover have "\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
                        (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, (\<Sigma>g',\<Sigma>l')))"
      using calculation(1) \<Sigma>b a9' Awaitc[OF \<Sigma>b _] v_eq by fastforce   
    moreover have "(\<Gamma>\<^sub>c,(Skip, ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Skip,((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
      using Skip_sim[OF a2 _ a4 a6  ] step_cs by blast
    ultimately show ?thesis using a1 a12 a2 a9 a9' c1  by fast
qed 

lemma spec_await_sim:assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and  
 a9: "C = Spec f v" and  a9': "S = Await bs Cs v" and 
 a11:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<sigma>g' \<sigma>l' \<Sigma>g \<Sigma>l \<Sigma>ls. (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls))\<in>\<xi> \<and> 
       (Skip,  (\<sigma>g',\<sigma>l')) \<in> com_step  C (\<sigma>g,\<sigma>l)  \<Gamma>\<^sub>c \<longrightarrow>  
       (\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls),  (s,\<Sigma>ls)) \<in> \<xi> } \<inter> bs \<inter> {fst((\<Sigma>g,\<Sigma>l),\<Sigma>ls)}) Cs 
         ({s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (s,\<Sigma>ls)) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>n',\<Sigma>ls))\<in> \<gamma>\<^sub>n}), {})" and 
  a12: "(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi> " and  a13:"Range \<xi> \<subseteq> {s. fst s \<in> bs}" and 
a14:"\<forall>\<Sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal \<Sigma>\<rangle> \<Rightarrow> Semantic.Fault f" and
a15: "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (C, (\<sigma>g,\<sigma>l)) \<rightarrow> (Skip, (\<sigma>g',\<sigma>l'))" and
a16:"(((\<sigma>g,\<sigma>l),\<sigma>ls),  (((\<sigma>g',\<sigma>l')), \<sigma>ls))\<in>G\<^sub>c"  
shows "\<exists>c1' \<Sigma>g' \<Sigma>l'. 
         (\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S,  (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
         (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c1',  (\<Sigma>g',\<Sigma>l')))) \<and>
         (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<alpha> \<and>
         (((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls)), (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
        (\<Gamma>\<^sub>c,(Skip, ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1', ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
proof-
  have v_eq:"v1 = v" using a15 a9
    using label_step by fastforce
  have a12': "((\<sigma>g,\<sigma>l),\<sigma>ls)\<in>Domain \<xi>" using a12 by auto
  have \<Sigma>inbs: "(\<Sigma>g,\<Sigma>l)\<in>bs" using a13 a12 by auto
  then have a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (Spec f v, (\<sigma>g,\<sigma>l)) \<rightarrow> (Skip, (\<sigma>g',\<sigma>l'))" using a15 a9  v_eq by auto
  then have  \<sigma>:"( (\<sigma>g,\<sigma>l),(\<sigma>g',\<sigma>l') )\<in>f"   
    using CRef.stepc_elim_cases(2) a00 spec_skip stepce_stepc by auto    
  then have " (Skip, (\<sigma>g',\<sigma>l'))  \<in> com_step  C (\<sigma>g,\<sigma>l) \<Gamma>\<^sub>c" using a9 by auto
  then have " \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls),  (s,\<Sigma>ls)) \<in> \<xi> } \<inter> bs \<inter> {fst((\<Sigma>g,\<Sigma>l),\<Sigma>ls)}) Cs 
         ({s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (s,\<Sigma>ls)) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>n',\<Sigma>ls))\<in> \<gamma>\<^sub>n}), {}"
    using a12 a11 by blast
  then have "\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls),  (s,\<Sigma>ls)) \<in> \<xi> } \<inter> bs \<inter> {fst((\<Sigma>g,\<Sigma>l),\<Sigma>ls)}) Cs 
         ({s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (s,\<Sigma>ls)) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>n',\<Sigma>ls))\<in> \<gamma>\<^sub>n}), {}"
    using hoaret_sound' by blast  
  moreover have \<Sigma>b:"(\<Sigma>g,\<Sigma>l)\<in>bs"  using  a12 a13 by fastforce
  ultimately obtain \<Sigma>g' \<Sigma>l' where step_cs:
    "\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal (\<Sigma>g,\<Sigma>l)\<rangle> \<Rightarrow> Normal (\<Sigma>g',\<Sigma>l') \<and> 
    (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)) \<in> \<gamma>\<^sub>n \<and> 
    (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)) \<in>G\<^sub>s "
    using a12 a14 Termination.terminates_implies_exec[of "\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a" Cs "Normal (\<Sigma>g,\<Sigma>l)"]  
    unfolding validt_def valid_def    
      by fastforce    
   moreover have " (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls))\<in> G\<^sub>c" using a16 \<sigma>
      by fastforce
  then have "((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls)), (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>" 
      using calculation(1) a1 a12 a2 unfolding related_transitions_def by fastforce
    moreover have "\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
                        (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, (\<Sigma>g',\<Sigma>l')))"
      using calculation(1) \<Sigma>b a9' Awaitc[OF \<Sigma>b _] v_eq by fastforce   
    moreover have "(\<Gamma>\<^sub>c,(Skip, ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Skip,((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
      using Skip_sim[OF a2 _ a4 a6  ] step_cs by blast
    ultimately show ?thesis using a1 a12 a2 a9 a9' c1  by fast
qed 



lemma basic_spec_await_sim:assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and  
  a9:"C = Basic fc v \<or> C = Spec rc v" and 
 a9': "S = Await bs Cs v" and  
 a10:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<sigma>g' \<sigma>l' . ((\<sigma>g, \<sigma>l), \<sigma>ls) \<in>Domain \<xi> \<and> 
        (Skip, (\<sigma>g', \<sigma>l')) \<in> com_step C (\<sigma>g, \<sigma>l) \<Gamma>\<^sub>c \<longrightarrow> 
          (((\<sigma>g, \<sigma>l), \<sigma>ls), ((\<sigma>g', \<sigma>l'), \<sigma>ls))\<in>G\<^sub>c" and
a11:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<sigma>g' \<sigma>l' \<Sigma>g \<Sigma>l \<Sigma>ls. (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls))\<in>\<xi> \<and> 
       (Skip,  (\<sigma>g',\<sigma>l')) \<in> com_step  C (\<sigma>g,\<sigma>l)  \<Gamma>\<^sub>c \<longrightarrow>  
       (\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls),  (s,\<Sigma>ls)) \<in> \<xi> } \<inter> bs \<inter> {fst((\<Sigma>g,\<Sigma>l),\<Sigma>ls)}) Cs 
         ({s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (s,\<Sigma>ls)) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>n',\<Sigma>ls))\<in> \<gamma>\<^sub>n}), {})" and 
a12:"\<forall>\<Sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal \<Sigma>\<rangle> \<Rightarrow> Semantic.Fault f" and
 a13: "(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi> " and  a14:"Range \<xi> \<subseteq> {s. fst s \<in> bs}" and
a15: "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (C, (\<sigma>g,\<sigma>l)) \<rightarrow> (Skip, (\<sigma>g',\<sigma>l'))"
shows "\<exists>c1' \<Sigma>g' \<Sigma>l'. 
         (\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S,  (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
         (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c1',  (\<Sigma>g',\<Sigma>l')))) \<and>
         (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<alpha> \<and>
         (((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls)), (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
        (\<Gamma>\<^sub>c,(Skip, ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1', ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
proof-
  have a12': "((\<sigma>g,\<sigma>l),\<sigma>ls)\<in>Domain \<xi>" using a13 by auto  
  { assume a00:"C = Basic fc v"
    then have h1:" (((\<sigma>g, \<sigma>l), \<sigma>ls), fc (\<sigma>g, \<sigma>l), \<sigma>ls) \<in> G\<^sub>c" using a10 a15 apply auto
      by (metis Pair_inject a12' stepc_elim_cases1(5))    
    then have ?thesis 
      using  basic_await_sim[OF a1 a2 a2' a3 a4 a5 a6  a00 a9' a11 a13 a14 a12 a15 h1]  by auto    
  }
  moreover { assume a00:"C = Spec rc v"
    then have h1:" (((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g', \<sigma>l'), \<sigma>ls) \<in> G\<^sub>c" using a10 a15 apply auto
      by (metis  a12' stepc_elim_cases(2))  
    then have ?thesis 
      using spec_await_sim[OF a1 a2 a2' a3 a4 a5 a6  a00 a9' a11 a13 a14 a12 a15 h1] by auto
  }
  ultimately show ?thesis using a9 by auto   
qed

lemma Step_Basic_Spec_not_normal: 
  assumes a0:"C = Basic fc v \<or> C = Spec rc v" and 
      a1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (C, (\<sigma>g,\<sigma>l)) \<rightarrow> (C', (\<sigma>g',\<sigma>l'))" and
      a2:"C' \<noteq> Skip" and a3:"(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and
      a4:"\<forall>\<sigma>g \<sigma>l \<sigma>ls. ((\<sigma>g,\<sigma>l),\<sigma>ls) \<in> Domain \<xi> \<longrightarrow> 
            (\<exists>\<sigma>g' \<sigma>l' . ((\<sigma>g,\<sigma>l),(\<sigma>g',\<sigma>l'))\<in>rc)"
    shows "P"
proof-
  {assume a00: "C = Basic fc v"
    then have ?thesis using a1 a2
      by (meson Pair_inject stepc_elim_cases1(5) stepce_stepc)
  }
  moreover { 
    assume a00: "C = Spec rc v"
    then have ?thesis using a4 a3 a1 a2
      by (meson Domain.DomainI Pair_inject stepc_elim_cases1(6) stepce_stepc)
  }
  ultimately show ?thesis using a0 by auto 
qed

lemma mod_state_Await_Spec_Sim: 
  assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
  a6:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and  
 a9:"C = Basic fc v \<or> C = Spec rc v" and 
 a9': "S = Await bs Cs v" and  
a10:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<sigma>g' \<sigma>l' . ((\<sigma>g, \<sigma>l), \<sigma>ls) \<in>Domain \<xi> \<and> 
        (Skip, (\<sigma>g', \<sigma>l')) \<in> com_step C (\<sigma>g, \<sigma>l) \<Gamma>\<^sub>c \<longrightarrow> 
          (((\<sigma>g, \<sigma>l), \<sigma>ls), ((\<sigma>g', \<sigma>l'), \<sigma>ls))\<in>G\<^sub>c" and
 a11:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<sigma>g' \<sigma>l' \<Sigma>g \<Sigma>l \<Sigma>ls. (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls))\<in>\<xi> \<and> 
       (Skip,  (\<sigma>g',\<sigma>l')) \<in> com_step  C (\<sigma>g,\<sigma>l)  \<Gamma>\<^sub>c \<longrightarrow>  
       (\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
         ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls),  (s,\<Sigma>ls)) \<in> \<xi> } \<inter> bs \<inter> {fst((\<Sigma>g,\<Sigma>l),\<Sigma>ls)}) Cs 
         ({s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  (s,\<Sigma>ls)) \<in> G\<^sub>s} \<inter> {\<Sigma>n'. (((\<sigma>g',\<sigma>l'),\<sigma>ls),(\<Sigma>n',\<Sigma>ls))\<in> \<gamma>\<^sub>n}), {})" and 
a12:"\<forall>\<Sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cs,Normal \<Sigma>\<rangle> \<Rightarrow> Semantic.Fault f" and
  a14:"Range \<xi> \<subseteq> {s. fst s \<in> bs}" and
 a15:"\<forall>\<sigma>g \<sigma>l \<sigma>ls. ((\<sigma>g,\<sigma>l),\<sigma>ls) \<in> Domain \<xi> \<longrightarrow> 
            (\<exists>\<sigma>g' \<sigma>l' . ((\<sigma>g,\<sigma>l),(\<sigma>g',\<sigma>l'))\<in>rc)"
shows "(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)"    
proof-
  {fix \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls
    assume a16: "(((\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<in> \<xi>"   
    then have "(\<Gamma>\<^sub>c,(C, ((\<sigma>g, \<sigma>l), \<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)),R\<^sub>s,G\<^sub>s)" 
     apply (coinduction arbitrary:\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls)
      
      apply clarsimp
      apply (rule conjId)+ 
      using a9 apply fastforce+
         apply (meson a3 sim_env) unfolding toSeq_def
        apply (rule, rule, rule, rule, rule)
      subgoal for \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls v c\<^sub>c' a b
        apply (cases "c\<^sub>c' \<noteq> Skip")
         apply (auto dest: Step_Basic_Spec_not_normal[OF a9 _ _ _ a15])
        by (fastforce dest: basic_spec_await_sim[OF a1 a2 a2' a3 a4 a5 a6   a9 a9' a10 a11 a12 _ a14])
      unfolding toSeq_def
       apply (rule, rule, rule, rule)
      subgoal for \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls c\<^sub>c' a b
        apply (cases "c\<^sub>c' \<noteq> Skip")
         apply (auto dest: Step_Basic_Spec_not_normal[OF a9 _ _ _ a15])
        apply (frule basic_spec_await_sim[OF a1 a2 a2' a3 a4 a5 a6   a9 a9' a10 a11 a12 _ a14], fast)        
      using intro_tau_step by fast
      using a1  by auto
  }  then show ?thesis unfolding RGSim_pre_def  by auto
qed 

lemma await_basic_sim:assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and     
 a9:"C = Await bc Cc v" and  
a9': "S = Basic fc v" and
a10:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. (\<sigma>g,\<sigma>l) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Cc 
        ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s, \<sigma>ls)) \<in> G\<^sub>c} \<inter> 
         {s. \<exists>\<Sigma>g' \<Sigma>l'. (Skip, (\<Sigma>g',\<Sigma>l')) \<in> com_step S (\<Sigma>g, \<Sigma>l) \<Gamma>\<^sub>c \<and> 
             ((s,\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in> \<gamma>\<^sub>n \<and> 
             (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s}), {}"  and
a12: "(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi> " and  a13:"Domain \<xi> \<subseteq> {s. fst s \<in> bc}" and 
a15: "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (C, (\<sigma>g,\<sigma>l)) \<rightarrow> (c1, (\<sigma>g',\<sigma>l'))" and a16:"c1 = Skip \<or> c1 = Throw"
shows "\<exists>c1' \<Sigma>g' \<Sigma>l'. 
         (\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
         (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c1', (\<Sigma>g', \<Sigma>l')))) \<and>
         (((\<sigma>g',\<sigma>l'), \<sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)) \<in> \<alpha> \<and>
         (((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls)), (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
        (\<Gamma>\<^sub>c,(c1,  ((\<sigma>g',\<sigma>l'), \<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1', (\<Sigma>g',\<Sigma>l'),\<Sigma>ls),R\<^sub>s,G\<^sub>s)"
proof-
  have v_eq:"v1 = v" using a15 a9
    using label_step by fastforce
  have a12': "((\<sigma>g,\<sigma>l),\<sigma>ls)\<in>Domain \<xi>" using a12 by auto
  have \<sigma>inbs: "((\<sigma>g,\<sigma>l))\<in>bc" using a13 a12 by auto
  then have a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (Await bc Cc v,(\<sigma>g,\<sigma>l)) \<rightarrow> (c1, (\<sigma>g',\<sigma>l'))" using a15 a9  v_eq by auto
  {assume cSkip:"c1 = Skip"
   then have  \<sigma>:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Normal (\<sigma>g',\<sigma>l')"
     using a00 CRef.stepc_elim_cases1(10) a00 spec_skip stepce_stepc by fastforce
   then have a10:
    "\<forall>\<sigma>g \<sigma>l. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
       (bc \<inter> {s. (\<sigma>g,\<sigma>l) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Cc 
        ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s, \<sigma>ls)) \<in> G\<^sub>c} \<inter> 
         {s. \<exists>\<Sigma>g' \<Sigma>l'. (Skip, (\<Sigma>g',\<Sigma>l')) \<in> com_step S (\<Sigma>g, \<Sigma>l) \<Gamma>\<^sub>c \<and> 
             ((s,\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in> \<gamma>\<^sub>n \<and> 
             (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s}), {}"
     using a10 by auto   
   then obtain \<Sigma>g' \<Sigma>l' where 
    step_cs:"(Skip, (\<Sigma>g', \<Sigma>l')) \<in> com_step S (\<Sigma>g, \<Sigma>l) \<Gamma>\<^sub>c \<and> (((\<sigma>g',\<sigma>l'), \<sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls)\<in> \<gamma>\<^sub>n \<and> 
             (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'), \<sigma>ls))\<in> G\<^sub>c"     
     using a12 \<sigma>inbs 
        step_imp_normal_rel3[OF _ _ \<sigma>, of F bc \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls \<xi> G\<^sub>c 
            "{s. \<exists>\<Sigma>g' \<Sigma>l'. (Skip, (\<Sigma>g',\<Sigma>l')) \<in> com_step S (\<Sigma>g, \<Sigma>l) \<Gamma>\<^sub>c \<and> 
             ((s,\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in> \<gamma>\<^sub>n \<and> 
             (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s}" "{}"]      
     by auto   
   then have "(((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls)), (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)" 
      using  a1 a12 a2 unfolding related_transitions_def by fastforce
   moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (Basic fc v, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Skip, (\<Sigma>g',\<Sigma>l'))" 
     using Basicc v_eq a9' step_cs by auto
   then have "\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
                        (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, (\<Sigma>g',\<Sigma>l')))"
     using a9' by fastforce
   moreover have "(\<Gamma>\<^sub>c,(c1, ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Skip, ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
      using Skip_sim[OF a2 _ a4 a6 ] step_cs cSkip by blast
    ultimately have ?thesis using a2 step_cs by blast
  }
  moreover {
    assume cSkip:"c1 = Throw"
    then have  \<sigma>:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Abrupt (\<sigma>g',\<sigma>l')"
      using a00 CRef.stepc_elim_cases1(10) a00 spec_skip stepce_stepc by fastforce
    then have ?thesis using in_normal_not_abrupt [OF _ \<sigma>] \<sigma>inbs a12 a10 by blast
  } 
  ultimately show ?thesis using c1 a16 by auto
qed 

lemma await_spec_sim:assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and     
a9:"C = Await bc Cc v" and  
a9': "S = Spec rc v" and
a10:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. (\<sigma>g,\<sigma>l) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Cc 
        ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s, \<sigma>ls)) \<in> G\<^sub>c} \<inter> 
         {s. \<exists>\<Sigma>g' \<Sigma>l'. (Skip, (\<Sigma>g',\<Sigma>l')) \<in> com_step S (\<Sigma>g, \<Sigma>l) \<Gamma>\<^sub>c \<and> 
             ((s,\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in> \<gamma>\<^sub>n \<and> 
             (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s}), {}"  and
a12: "(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi> " and  a13:"Domain \<xi> \<subseteq> {s. fst s \<in> bc}" and 
a15: "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (C, (\<sigma>g,\<sigma>l)) \<rightarrow> (c1, (\<sigma>g',\<sigma>l'))" and a16:"c1 = Skip \<or> c1 = Throw"
shows "\<exists>c1' \<Sigma>g' \<Sigma>l'. 
         (\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
         (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c1', (\<Sigma>g', \<Sigma>l')))) \<and>
         (((\<sigma>g',\<sigma>l'), \<sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)) \<in> \<alpha> \<and>
         (((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls)), (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
        (\<Gamma>\<^sub>c,(c1,  ((\<sigma>g',\<sigma>l'), \<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1', (\<Sigma>g',\<Sigma>l'),\<Sigma>ls),R\<^sub>s,G\<^sub>s)"
proof-
  have v_eq:"v1 = v" using a15 a9
    using label_step by fastforce
  have a12': "((\<sigma>g,\<sigma>l),\<sigma>ls)\<in>Domain \<xi>" using a12 by auto
  have \<sigma>inbs: "((\<sigma>g,\<sigma>l))\<in>bc" using a13 a12 by auto
  then have a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (Await bc Cc v,(\<sigma>g,\<sigma>l)) \<rightarrow> (c1, (\<sigma>g',\<sigma>l'))" using a15 a9  v_eq by auto
  {assume cSkip:"c1 = Skip"
   then have  \<sigma>:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Normal (\<sigma>g',\<sigma>l')"
     using a00 CRef.stepc_elim_cases1(10) a00 spec_skip stepce_stepc by fastforce
   then have a10:
    "\<forall>\<sigma>g \<sigma>l. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
       (bc \<inter> {s. (\<sigma>g,\<sigma>l) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Cc 
        ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s, \<sigma>ls)) \<in> G\<^sub>c} \<inter> 
         {s. \<exists>\<Sigma>g' \<Sigma>l'. (Skip, (\<Sigma>g',\<Sigma>l')) \<in> com_step S (\<Sigma>g, \<Sigma>l) \<Gamma>\<^sub>c \<and> 
             ((s,\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in> \<gamma>\<^sub>n \<and> 
             (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s}), {}"
     using a10 by auto   
   then obtain \<Sigma>g' \<Sigma>l' where 
    step_cs:"(Skip, (\<Sigma>g', \<Sigma>l')) \<in> com_step S (\<Sigma>g, \<Sigma>l) \<Gamma>\<^sub>c \<and> (((\<sigma>g',\<sigma>l'), \<sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls)\<in> \<gamma>\<^sub>n \<and> 
             (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'), \<sigma>ls))\<in> G\<^sub>c"     
     using a12 \<sigma>inbs 
        step_imp_normal_rel3[OF _ _ \<sigma>, of F bc \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls \<xi> G\<^sub>c 
            "{s. \<exists>\<Sigma>g' \<Sigma>l'. (Skip, (\<Sigma>g',\<Sigma>l')) \<in> com_step S (\<Sigma>g, \<Sigma>l) \<Gamma>\<^sub>c \<and> 
             ((s,\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in> \<gamma>\<^sub>n \<and> 
             (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s}" "{}"]      
     by auto   
   then have "(((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls)), (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)" 
      using  a1 a12 a2 unfolding related_transitions_def by fastforce
   moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (Spec rc v, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Skip, (\<Sigma>g',\<Sigma>l'))" 
     using Specc v_eq a9' step_cs by auto
   then have "\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
                        (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, (\<Sigma>g',\<Sigma>l')))"
     using a9' by fastforce
   moreover have "(\<Gamma>\<^sub>c,(c1, ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Skip, ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
      using Skip_sim[OF a2 _ a4 a6 ] step_cs cSkip by blast
    ultimately have ?thesis using a2 step_cs by blast
  }
  moreover {
    assume cSkip:"c1 = Throw"
    then have  \<sigma>:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Abrupt (\<sigma>g',\<sigma>l')"
      using a00 CRef.stepc_elim_cases1(10) a00 spec_skip stepce_stepc by fastforce
    then have ?thesis using in_normal_not_abrupt [OF _ \<sigma>] \<sigma>inbs a12 a10 by blast
  } 
  ultimately show ?thesis using c1 a16 by auto
qed 

lemma await_basic_spec_sim:assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
a6:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and  
a9:"C = Await bc Cc v" and    
a9':"S = Basic fc v \<or> S = Spec rc v" and  
a10:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. (\<sigma>g,\<sigma>l) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Cc 
        ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s, \<sigma>ls)) \<in> G\<^sub>c} \<inter> 
         {s. \<exists>\<Sigma>g' \<Sigma>l'. (Skip, (\<Sigma>g',\<Sigma>l')) \<in> com_step S (\<Sigma>g, \<Sigma>l) \<Gamma>\<^sub>c \<and> 
             ((s,\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in> \<gamma>\<^sub>n \<and> 
             (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s}), {}"  and
a12: "(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi> " and  a13:"Domain \<xi> \<subseteq> {s. fst s \<in> bc}" and 
a15: "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>v1 (C, (\<sigma>g,\<sigma>l)) \<rightarrow> (c1, (\<sigma>g',\<sigma>l'))" and a16:"c1 = Skip \<or> c1 = Throw"
shows "\<exists>c1' \<Sigma>g' \<Sigma>l'. 
         (\<exists>a b. (\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, b)) \<and>
         (\<exists>aa ba. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v1 (a, b) \<rightarrow> (aa, ba) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, ba) \<rightarrow>\<^sub>\<tau>\<^sup>* (c1', (\<Sigma>g', \<Sigma>l')))) \<and>
         (((\<sigma>g',\<sigma>l'), \<sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)) \<in> \<alpha> \<and>
         (((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls)), (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
        (\<Gamma>\<^sub>c,(c1,  ((\<sigma>g',\<sigma>l'), \<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c1', (\<Sigma>g',\<Sigma>l'),\<Sigma>ls),R\<^sub>s,G\<^sub>s)"
proof-
  have a12': "((\<sigma>g, \<sigma>l),\<sigma>ls)\<in>Domain \<xi>" using a12 by auto  
  then show ?thesis 
    using a9'  await_basic_sim[OF a1 a2 a2' a3 a4 a5 a6   a9 _ a10 a12 a13 a15 a16] 
              await_spec_sim[OF a1 a2 a2' a3 a4 a5 a6   a9 _ a10 a12 a13 a15 a16]
    by auto
qed

lemma Step_Await_not_normal1: 
  assumes  
      a1:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (Await bc Cc v, (\<sigma>g,\<sigma>l)) \<rightarrow> (c\<^sub>c', (\<sigma>g',\<sigma>l'))" and
      a2:"c\<^sub>c' \<noteq> Skip" and a3:"(((\<sigma>g,\<sigma>l), \<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and
      a4:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. (\<sigma>g,\<sigma>l) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Cc 
        ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s, \<sigma>ls)) \<in> G\<^sub>c} \<inter> 
         {s. \<exists>\<Sigma>g' \<Sigma>l'. (Skip, (\<Sigma>g',\<Sigma>l')) \<in> com_step S (\<Sigma>g, \<Sigma>l) \<Gamma>\<^sub>c \<and> 
             ((s,\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in> \<gamma>\<^sub>n \<and> 
             (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s}), {}" and
     a5:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Semantic.Fault f"
    shows "P"
proof-
  obtain \<sigma>' where step: "\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> \<sigma>' \<and> (\<sigma>g,\<sigma>l)\<in>bc \<and> (\<forall>na. \<sigma>' \<noteq> Normal na)" 
    using a2
    apply (cases c\<^sub>c', auto) using a1  stepce_stepc 
    by (auto intro: stepc_elim_cases1(10))+  
  thus ?thesis using  a2 a3 a5 a4
     by (blast intro: not_normal_false)
qed

lemma mod_state_Await_Impl_Sim: 
  assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<gamma>\<^sub>n \<subseteq> \<alpha>" and a2':"\<gamma>\<^sub>a \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<gamma>\<^sub>n ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a5:"Sta\<^sub>s \<gamma>\<^sub>a ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and  
 a9:"C = Await bc Cc v" and    
a9':"S = Basic fc v \<or> S = Spec rc v" and  
a10:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (bc \<inter> {s. (\<sigma>g,\<sigma>l) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Cc 
        ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s, \<sigma>ls)) \<in> G\<^sub>c} \<inter> 
         {s. \<exists>\<Sigma>g' \<Sigma>l'. (Skip, (\<Sigma>g',\<Sigma>l')) \<in> com_step S (\<Sigma>g, \<Sigma>l) \<Gamma>\<^sub>c \<and> 
             ((s,\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in> \<gamma>\<^sub>n \<and> 
             (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s}), {}"  and
a12: "(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi> " and  a13:"Domain \<xi> \<subseteq> {s. fst s \<in> bc}" and
a12:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Semantic.Fault f" 
shows "(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)"    
proof-
  {fix \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls
    assume "(((\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<in> \<xi>"   
    then have "(\<Gamma>\<^sub>c,(C, ((\<sigma>g, \<sigma>l), \<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)),R\<^sub>s,G\<^sub>s)" 
     apply (coinduction arbitrary: \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls)
      
      apply clarsimp
      apply (rule conjId)+       
      using a9 apply fastforce+
         apply (meson a3 sim_env) 
         unfolding toSeq_def
        apply (rule, rule, rule, rule, rule)
         subgoal for \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls v c\<^sub>c' a b
           apply (cases "c\<^sub>c' \<noteq> Skip")
           using a9
            apply (auto dest: Step_Await_not_normal1[OF _ _  _ a10 a12])  
           by (fast dest:await_basic_spec_sim[OF a1 a2 a2' a3 a4 a5 a6 a9 a9' a10 _ a13])
          apply (rule, rule, rule, rule)
         subgoal for \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls  c\<^sub>c' a b
           apply (cases "c\<^sub>c' \<noteq> Skip")
           using a9
            apply (auto dest: Step_Await_not_normal1[OF _ _  _ a10 a12])  
           apply (frule await_basic_spec_sim[OF a1 a2 a2' a3 a4 a5 a6 a9 a9' a10 _ a13], fast, fast)
            using intro_tau_step by fast
      using a1  by auto
  }  then show ?thesis unfolding RGSim_pre_def  by auto
qed

lemma Seq_skip_C:
  assumes 
    a0:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (Seq Skip C, (\<sigma>g,\<sigma>l)) \<rightarrow> (c\<^sub>c',  (\<sigma>g',\<sigma>l'))" 
  shows "c\<^sub>c' = C \<and>  (\<sigma>g',\<sigma>l') = (\<sigma>g,\<sigma>l) \<and> e = \<tau>"
  using a0
  apply (rule stepc_elim_seq_skip(1))
  apply (meson stepc_elim_cases1(1))
  by auto

lemma Seq_final_not_skip_C:
 assumes 
    a0:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>e (Seq C C', (\<sigma>g,\<sigma>l)) \<rightarrow> (c\<^sub>c',  (\<sigma>g',\<sigma>l'))" and a1:"C = Throw \<or> C = Stuck \<or> (\<exists>f. C = Fault f)"
  shows "c\<^sub>c' = C \<and>  (\<sigma>g',\<sigma>l') = (\<sigma>g,\<sigma>l) \<and> e = \<tau>"
  using a0 a1
  by (auto intro:stepc_elim_seq_skip(2,3,4) stepc_elim_cases1(2,3,13))

lemma Impl_Skip_sim2: 
  assumes  
 a0:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and
 a3: "(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)" and
 a4:"(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and
 a5:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Seq Skip C, (\<sigma>g,\<sigma>l)) \<rightarrow> (c\<^sub>c', (\<sigma>g',\<sigma>l'))"
shows "\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g, \<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',(\<Sigma>g', \<Sigma>l')) \<and>
          (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<in> \<alpha> \<and>
          (((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          (c\<^sub>c' = Seq LanguageCon.com.Skip C \<and> c\<^sub>s' = S \<and> (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<in> \<xi> \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)),R\<^sub>s,G\<^sub>s))"
proof -                                               
  have C:"c\<^sub>c' = C" and sigma:"(\<sigma>g',\<sigma>l') = (\<sigma>g,\<sigma>l)"using Seq_skip_C[OF a5] by auto    
  have rfgs:"(((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls))\<in> G\<^sub>s\<^sup>*" by auto  
  have f1: "\<forall>a c. (a, c) \<notin> \<xi> \<or> (\<Gamma>\<^sub>c,(C,  a),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S,  c),R\<^sub>s,G\<^sub>s)"
    by (meson RGSim_pre_def a3)
  then have f2: "((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g,\<sigma>l),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
    using a0 rfgs a4 
    by (metis alpha_id_G dest_sim_alpha)
  have "(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<alpha>"
    using f1 a4 C sigma
    using dest_sim_alpha by blast
  then show ?thesis
    using f2 f1 sigma C  a4 by blast
qed      
   


lemma Impl_Seq_Skip_sim: assumes a0:"\<xi> \<subseteq> \<alpha>" and 
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and
 a8: "(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)" 
shows "(\<Gamma>\<^sub>c,Seq Skip C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)"
proof-
{fix \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls 
 assume a11: "(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>"    
 then have "(\<Gamma>\<^sub>c,(Seq Skip C, ((\<sigma>g,\<sigma>l),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
   apply (coinduction arbitrary:  \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls )
   apply simp
   apply (rule conjId)+
   apply (auto simp add: toSeq_def)
      apply (meson a3 sim_env)      
   apply (frule Seq_skip_C, auto)
    apply (frule Impl_Skip_sim2[OF a6  a8], auto)
   using a0 by auto   
} thus ?thesis unfolding RGSim_pre_def by auto
qed

lemma Impl_Skip_sim2':
  assumes
    a4: "(\<Gamma>\<^sub>c,(C, ((\<sigma>g,\<sigma>l),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)" and          
    a6:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Seq C Skip,  (\<sigma>g,\<sigma>l)) \<rightarrow> (c\<^sub>c', (\<sigma>g',\<sigma>l'))"
shows  "\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
          (\<exists>a b c. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, (b,c)) \<and>
                 (\<exists>aa ba bb. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, (b,c)) \<rightarrow> (aa, (ba,bb)) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, (ba,bb)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', (\<Sigma>g',\<Sigma>l')))) \<and>
          (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<in> \<alpha> \<and>
         (((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)) \<and>
          ((\<exists>C. c\<^sub>c' = Seq C Skip \<and> 
              (\<Gamma>\<^sub>c,(C, ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)) \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s))"
proof-    
  have in_alpha:"(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls))\<in> \<alpha>" using a4
    using dest_sim_alpha by blast
  {assume a00:"C = Skip \<or> C = Throw \<or> C = Stuck \<or> (\<exists>f. C = Fault f)"    
    then have ?thesis  using not_seq_skip_throw_ev a6[simplified a00]
      by metis
  } 
  moreover { assume a00:"C\<noteq>Skip \<and> C\<noteq>Throw \<and> C \<noteq> Stuck \<and> (\<forall>f. C \<noteq> Fault f)"  
    let ?\<sigma> = "((\<sigma>g,\<sigma>l),\<sigma>ls)"  and ?\<sigma>' =  "((\<sigma>g',\<sigma>l'),\<sigma>ls)"
    obtain C' where step:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C,  (\<sigma>g,\<sigma>l)) \<rightarrow> (C', (\<sigma>g',\<sigma>l')) \<and> 
                          c\<^sub>c' = Seq C' Skip" 
      using stepc_elim_cases1(7)[OF a6] by auto
    moreover obtain \<Sigma>g' \<Sigma>l' c\<^sub>s' where 
     " \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (S,  (\<Sigma>g, \<Sigma>l)) \<rightarrow>\<^sup>+ (c\<^sub>s', (\<Sigma>g', \<Sigma>l')) \<and> (?\<sigma>', ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<in> \<alpha> \<and>
        (((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)) \<and> 
       (\<Gamma>\<^sub>c,(C', ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)" 
      using dest_sim_ev_step[OF a4] step a6 unfolding toSeq_def by fastforce      
    ultimately have ?thesis  by fastforce
  } ultimately show ?thesis by fastforce
qed  


lemma Impl_Seq_Skip_sim3':
  assumes     
    a2:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and
    a4: "(\<Gamma>\<^sub>c,(C, ((\<sigma>g,\<sigma>l),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)" and     
    a5:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Seq C Skip, (\<sigma>g,\<sigma>l)) \<rightarrow> (c\<^sub>c', (\<sigma>g',\<sigma>l'))" 
     shows
       "\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', (\<Sigma>g',\<Sigma>l')) \<and>
          (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<in> \<alpha> \<and>
         (((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)) \<and>
          ((\<exists>C. c\<^sub>c' = Seq C Skip \<and> 
              (\<Gamma>\<^sub>c,(C, ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)) \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s))"
proof-
  have in_alpha:"(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls))\<in> \<alpha>" using a4
    using dest_sim_alpha by blast
  let ?\<sigma>s = "(\<sigma>g,\<sigma>l)" and ?\<sigma>s' = "(\<sigma>g',\<sigma>l')" let ?\<sigma> = "(?\<sigma>s,\<sigma>ls)"  and ?\<sigma>' = "(?\<sigma>s',\<sigma>ls)"
  let ?\<Sigma>s = "(\<Sigma>g,\<Sigma>l)"  let ?\<Sigma> = "(?\<Sigma>s,\<Sigma>ls)" 
  { assume a00:"C = Skip"    
    then have  eq:"c\<^sub>c' = Skip \<and> ?\<sigma>' = ?\<sigma>" using Seq_skip_C[OF a5[simplified a00]] by auto      
    moreover have  "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, ?\<Sigma>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (S, ?\<Sigma>s)" by auto
     moreover have  "((\<exists>C. Skip = Seq C Skip \<and> (\<Gamma>\<^sub>c,(C, ?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, ?\<Sigma>),R\<^sub>s,G\<^sub>s)) \<or>
        (\<Gamma>\<^sub>c,(Skip, ?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, ?\<Sigma>),R\<^sub>s,G\<^sub>s))"
       using a4 a00 by fastforce 
     moreover have "(((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>))"
       unfolding related_transitions_def using a2 eq in_alpha by fastforce
     ultimately have ?thesis using a4 eq in_alpha by fastforce
  } 
  moreover {assume a00:"C=Throw \<or> C = Stuck \<or> (\<exists>f. C = Fault f)" 
    then have  eq:"c\<^sub>c' = C \<and> ?\<sigma>' = ?\<sigma>"
      using Seq_final_not_skip_C[OF a5 a00] by auto 
     moreover have  "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, ?\<Sigma>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (S, ?\<Sigma>s)" by auto
     moreover have  
      "((\<exists>C'. C = LanguageCon.com.Seq C' C \<and> (\<Gamma>\<^sub>c,(C', ?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, ?\<Sigma>),R\<^sub>s,G\<^sub>s)) \<or>
        (\<Gamma>\<^sub>c,(C, ?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, ?\<Sigma>),R\<^sub>s,G\<^sub>s))"
       using a4 a00 by fastforce 
     moreover have "(((?\<sigma>, ?\<sigma>'), (?\<Sigma>, (\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>))"
       unfolding related_transitions_def using a2 eq in_alpha by fastforce
     ultimately have ?thesis using a4 eq in_alpha by fastforce
  }
  moreover{ 
    assume a00:"C\<noteq>Skip \<and> C\<noteq>Throw \<and> C \<noteq> Stuck \<and> (\<forall>f. C \<noteq> Fault f)"  
    then obtain C' where step:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (C, ?\<sigma>s) \<rightarrow> (C',  ?\<sigma>s') \<and> 
                               c\<^sub>c' = Seq C' Skip" 
      using stepc_elim_cases1(7)[OF a5] by auto 
    moreover obtain \<Sigma>g'  \<Sigma>l' c\<^sub>s' where 
     "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, ?\<Sigma>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', (\<Sigma>g', \<Sigma>l')) \<and>
      (?\<sigma>',((\<Sigma>g', \<Sigma>l'),\<Sigma>ls)) \<in> \<alpha> \<and>
      (((?\<sigma>, ?\<sigma>'), (?\<Sigma>, (\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)) \<and> 
      (\<Gamma>\<^sub>c,(C', ?\<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)" 
      using dest_sim_tau_step[OF a4] step a5 unfolding toSeq_def by fastforce      
    ultimately have ?thesis  by fastforce
  } ultimately show ?thesis by fastforce
qed

lemma Impl_Seq_Skip_sim'4:
  assumes a0:"(\<Gamma>\<^sub>c,(C, ((\<sigma>g,\<sigma>l),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)" and
       a1:"((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)), (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))) \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>"        
     shows "(\<Gamma>\<^sub>c,(C, ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S,((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s) \<or>
       (\<Gamma>\<^sub>c,(Seq C Skip, ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
  using a0 a1 dest_sim_env_step by blast

lemma Impl_Seq_Skip_sim': assumes a0:"\<xi> \<subseteq> \<alpha>" and 
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and
 a8: "(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)" 
shows "(\<Gamma>\<^sub>c,Seq C Skip,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)"
proof-
{ fix \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls 
  assume a11: "(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>"    
  then have  "(\<Gamma>\<^sub>c,(C,((\<sigma>g,\<sigma>l),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S,((\<Sigma>g,\<Sigma>l),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)" 
    using a8 unfolding RGSim_pre_def by auto
 then have "(\<Gamma>\<^sub>c,(Seq C Skip, ((\<sigma>g,\<sigma>l),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
   apply (coinduction arbitrary: \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls  C S)
   apply simp
   apply (rule conjId)+
        apply (rule, rule, rule, rule, rule, rule, rule)
   using dest_sim_env_step apply blast    
   apply (rule, rule,rule, rule, rule) unfolding toSeq_def       
   apply (frule Impl_Skip_sim2' , fastforce+)
      apply (rule, rule, rule, rule)
     apply (frule Impl_Seq_Skip_sim3'[OF a6], fastforce+)
   by (meson dest_sim_alpha)   
} thus ?thesis unfolding RGSim_pre_def by auto
qed

lemma Impl_Seq_Throw_sim2: 
  assumes  
 a0:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and
 a3: "(\<Gamma>\<^sub>c,F,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)" and a3':"F = Throw \<or> F = Stuck \<or> (\<exists>f. F = Fault f)" and
 a4:"(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and
 a5:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Seq F C, (\<sigma>g,\<sigma>l)) \<rightarrow> (c\<^sub>c', (\<sigma>g',\<sigma>l'))"
shows "\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g, \<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',(\<Sigma>g', \<Sigma>l')) \<and>
          (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<in> \<alpha> \<and>
          (((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          (c\<^sub>c' = Seq F C \<and> c\<^sub>s' = S \<and> (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<in> \<xi> \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)),R\<^sub>s,G\<^sub>s))"  
proof -
  have a00:"c\<^sub>c' = F \<and>  (\<sigma>g',\<sigma>l') = (\<sigma>g,\<sigma>l)" 
    using Seq_final_not_skip_C[OF a5 a3']  by auto      
  have rfgs:"(((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls))\<in> G\<^sub>s\<^sup>*" by auto  
  have f1: "\<forall>a c. (a, c) \<notin> \<xi> \<or> (\<Gamma>\<^sub>c,(F,  a),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S,  c),R\<^sub>s,G\<^sub>s)"
    by (meson RGSim_pre_def a3)
  then have f2: "((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g,\<sigma>l),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
    using a0 rfgs a4 
    by (metis alpha_id_G dest_sim_alpha)
  have "(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<alpha>"
    using f1 a4 a00 
    using dest_sim_alpha by blast
  then show ?thesis
    using f2 f1 a4 a00 by blast
qed      

lemma Impl_Seq_Throw_sim: assumes a0:"\<xi> \<subseteq> \<alpha>" and 
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and
 a8: "(\<Gamma>\<^sub>c,F,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)" and a8':"F = Throw \<or> F = Stuck \<or> (\<exists>f. F = Fault f)"
shows "(\<Gamma>\<^sub>c,Seq F C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)"
proof-
  { fix \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls 
    assume a11: "(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>"    
      then have "(\<Gamma>\<^sub>c,(Seq F C, ((\<sigma>g,\<sigma>l),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"     
        apply (coinduction arbitrary: \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls )
        apply simp
        apply (rule conjId)+
           apply (rule, rule, rule, rule, rule, rule, rule)
           apply (meson a3 sim_env)
          apply auto[1] unfolding toSeq_def
          apply (simp add: surjective_pairing)
          apply (frule Seq_final_not_skip_C[OF _ a8'], auto)[1] 
         apply auto[1]
         apply (frule Impl_Seq_Throw_sim2[OF a6 a8 a8'], fast, fast) 
        using a0 by auto
    } thus ?thesis unfolding RGSim_pre_def by auto
qed

lemma mod_state_tran_v: 
  "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>Some v (Seq C1 C2, (\<sigma>g,\<sigma>l)) \<rightarrow> (c\<^sub>c', (\<sigma>g',\<sigma>l')) \<Longrightarrow> 
   label C1 = \<tau> \<Longrightarrow>           
   \<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
      (\<exists>a b c. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, (b,c)) \<and>
             (\<exists>aa ba bb. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, (b,c)) \<rightarrow> (aa, (ba,bb)) \<and> 
      \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, (ba,bb)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', (\<Sigma>g',\<Sigma>l')))) \<and>
      (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<in> \<alpha> \<and>
     (((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)) \<and>
      (c\<^sub>c' = Seq C1 C2 \<and> c\<^sub>s' = S \<and> (((\<sigma>g',\<sigma>l'),\<sigma>ls), (\<Sigma>g,\<Sigma>l),\<Sigma>ls) \<in> \<xi> \<or> 
      (\<Gamma>\<^sub>c,(c\<^sub>c', ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',((\<Sigma>g,\<Sigma>l),\<Sigma>ls)),R\<^sub>s,G\<^sub>s))"
proof -
  assume a1: "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>Some v (Seq C1 C2, (\<sigma>g,\<sigma>l)) \<rightarrow> (c\<^sub>c', (\<sigma>g',\<sigma>l'))"
  assume a2: "label C1 = \<tau>"
  obtain c1' where s:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C1, (\<sigma>g,\<sigma>l)) \<rightarrow> (c1',(\<sigma>g',\<sigma>l'))" 
    using stepc_elim_cases1(7)[OF a1] by fastforce    
  thus ?thesis using label_step[OF _ s] a2 by force 
qed



lemma mod_state_only_spec_basic_tau_sound2:
  assumes 
    a0:"\<xi> \<subseteq> \<alpha> " and a0':"\<xi>\<^sub>1 \<subseteq> \<alpha> " and a1:"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and 
    a2:"(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and 
    a3:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<sigma>g' \<sigma>l' \<sigma>ls' \<Sigma>g  \<Sigma>l \<Sigma>ls C. 
         (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls))\<in>\<xi> \<and>  (C,(\<sigma>g',\<sigma>l')) \<in> com_step  C1 (\<sigma>g,\<sigma>l)  \<Gamma>\<^sub>c  \<longrightarrow> 
            C = Skip \<and> (((\<sigma>g',\<sigma>l'),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls))\<in>\<xi>\<^sub>1 \<and> 
            (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)) \<in> G\<^sub>c" and
    a4:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Seq C1 C2,  (\<sigma>g,\<sigma>l)) \<rightarrow> (c\<^sub>c', (\<sigma>g',\<sigma>l'))" and
    a5:"C1 = Basic fc \<tau> \<or> C1 = Spec rc \<tau>" and 
    a6:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and  
    a8:"(\<Gamma>\<^sub>c,C2,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)" 
  shows "\<exists>c\<^sub>s' aa ba.
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, \<Sigma>g, \<Sigma>l) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', aa, ba) \<and>
              (((\<sigma>g',\<sigma>l'), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
              ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g',\<sigma>l'), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
              (c\<^sub>c' = LanguageCon.com.Seq C1 C2 \<and> c\<^sub>s' = S \<and> (((\<sigma>g',\<sigma>l'), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or> 
              (\<Gamma>\<^sub>c,(c\<^sub>c', (\<sigma>g',\<sigma>l'), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s))"
proof-
  have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (S, (\<Sigma>g,\<Sigma>l))" by auto
  moreover have "(((\<Sigma>g,\<Sigma>l), \<Sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> G\<^sub>s\<^sup>*"  by auto
  moreover have "c\<^sub>c' = Seq Skip C2 \<and> (((\<sigma>g',\<sigma>l'), \<sigma>ls), (\<Sigma>g,\<Sigma>l),\<Sigma>ls) \<in>\<xi>\<^sub>1 \<and> 
                 (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)) \<in> G\<^sub>c" 
                 using a5
  proof
    assume a00:"C1 = LanguageCon.com.Basic fc \<tau> "    
    then have "c\<^sub>c' = Seq Skip C2" using stepc_elim_cases1(7)[OF a4] stepc_elim_cases1(5)
      by (metis LanguageCon.com.distinct(1) LanguageCon.com.distinct(37) 
              LanguageCon.com.distinct(43) LanguageCon.com.distinct(45) fst_conv) 
    moreover have "(((\<sigma>g',\<sigma>l'), \<sigma>ls), (\<Sigma>g,\<Sigma>l),\<Sigma>ls)\<in>\<xi>\<^sub>1 \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)) \<in> G\<^sub>c"  
    proof -
      have "(\<sigma>g',\<sigma>l') = fc (\<sigma>g,\<sigma>l)" using a4[simplified calculation a00]
        by (meson CRef.stepc_elim_cases(6) Pair_inject stepc_elim_cases1(5) 
               stepce_stepc xstate.inject(1))
      then show ?thesis using a3[simplified a00] a2 by auto
    qed
    ultimately show ?thesis by auto    
  next
    assume a00:"C1 = LanguageCon.com.Spec rc \<tau>"
    have c\<^sub>c':"c\<^sub>c' = Seq Skip C2" using stepc_elim_cases1(7)[OF a4[simplified a00]]
    proof -
      obtain cc xx where
        f1: "(c\<^sub>c', (\<sigma>g',\<sigma>l')) = (LanguageCon.com.Seq cc C2, xx) \<and> 
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Spec rc \<tau>, (\<sigma>g,\<sigma>l)) \<rightarrow> (cc, xx)"
        using stepc_elim_cases1(7)[OF a4[simplified a00]]  by force
      moreover have "(cc,(\<sigma>g',\<sigma>l'))\<in> com_step  C1 (\<sigma>g,\<sigma>l)  \<Gamma>\<^sub>c" 
        using a00 calculation Spec_r_com_step by fast
      ultimately show ?thesis
        using  a3 a2 by auto
    qed
    moreover have "(((\<sigma>g',\<sigma>l'),\<sigma>ls), (\<Sigma>g,\<Sigma>l),\<Sigma>ls)\<in>\<xi>\<^sub>1 \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)) \<in> G\<^sub>c"  
    proof-
      have "((\<sigma>g,\<sigma>l), (\<sigma>g',\<sigma>l'))\<in>rc" using a4[simplified calculation a00]
        by (meson CRef.stepc_elim_cases(2) CRef.stepc_elim_cases(6)) 
      then show ?thesis  using a3[simplified a00] a2
        by (metis Spec_r_com_step a00 a4 calculation evstepc_elim_seq(1)) 
    qed
    ultimately show ?thesis  by auto          
  qed

  moreover have "(\<Gamma>\<^sub>c,(c\<^sub>c', ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S,((\<Sigma>g,\<Sigma>l),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
    using Impl_Seq_Skip_sim[OF a0' a1 a6    a8] calculation 
    unfolding RGSim_pre_def by auto
  ultimately show ?thesis using a0' a0 a2 unfolding related_transitions_def by fast
qed

lemma imp_seq_Basic_Spec_sim: 
  assumes
  a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and
  a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
  a5:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and   
  a9:"C1 = Basic fc \<tau> \<or> C1 = Spec rc \<tau>" and   
  a10:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<sigma>g' \<sigma>l' \<sigma>ls' \<Sigma>g  \<Sigma>l \<Sigma>ls C. 
         (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls))\<in>\<xi> \<and>  (C,(\<sigma>g',\<sigma>l')) \<in> com_step  C1 (\<sigma>g,\<sigma>l)  \<Gamma>\<^sub>c  \<longrightarrow> 
            C= Skip \<and> (((\<sigma>g',\<sigma>l'),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls))\<in>\<xi>\<^sub>1 \<and> 
            (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)) \<in> G\<^sub>c" and
  a11:"(\<Gamma>\<^sub>c,C2,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)"
shows "(\<Gamma>\<^sub>c,Seq C1 C2 ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)"  
  
proof-
  {fix \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls 
    assume a12: "(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>"    
    then have "(\<Gamma>\<^sub>c,(Seq C1 C2,((\<sigma>g,\<sigma>l),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
      apply (coinduction arbitrary: \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls)
      apply clarsimp
      apply (rule conjId)+ 
      apply (rule, rule, rule, rule, rule, rule, rule)
      apply (meson a3 sim_env)
           apply (rule, rule, rule, rule, rule)
      unfolding toSeq_def apply auto[1]
        apply (frule mod_state_tran_v;  insert a9, fastforce+)      
      apply(rule, rule, rule, rule) apply (simp add: fst_def)
       apply (frule mod_state_only_spec_basic_tau_sound2[OF a1 a2 a4 _ a10 _ a9 a5   a11], fastforce)
      using a1 by auto   
  } then show ?thesis unfolding RGSim_pre_def by auto
qed

inductive_cases stepc_elim_casese:
 "\<Gamma>\<turnstile>\<^sub>c\<^sub>a(Await b c2 e, (\<sigma>g,\<sigma>l)) \<rightarrow> (nc, (\<sigma>g',\<sigma>l'))"

lemma mod_state_only_atomic_sound2:
  assumes a0:"\<xi> \<subseteq> \<alpha> " and a0':"\<xi>\<^sub>1 \<subseteq> \<alpha> " and a1:"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and 
          a2:"(((\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and 
      a3:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Seq C1 C2, (\<sigma>g,\<sigma>l)) \<rightarrow> (c\<^sub>c', (\<sigma>g',\<sigma>l'))" and        
      a9:"C1 = Await b Cc \<tau>" and   
      a4:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and 
      a8:"(\<Gamma>\<^sub>c,C2,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)" and      
      a10:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (b \<inter> {s. (\<sigma>g,\<sigma>l) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Cc
        ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s, \<sigma>ls)) \<in> G\<^sub>c \<and> ((s,\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls))\<in> \<xi>\<^sub>1}), {}"  and
    a7:"\<forall>\<sigma>g \<sigma>l. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal  (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Semantic.Fault f" 
  shows "(\<exists>c\<^sub>s' aa ba.
           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, \<Sigma>g, \<Sigma>l) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', aa, ba) \<and>
              (((\<sigma>g',\<sigma>l'), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
              ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g',\<sigma>l'), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          (c\<^sub>c' = LanguageCon.com.Seq C1 C2 \<and> c\<^sub>s' = S \<and>(((\<sigma>g',\<sigma>l'), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', (\<sigma>g',\<sigma>l'), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',(aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))"
proof-  
  have hoare:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
           (b \<inter> {s. (\<sigma>g,\<sigma>l) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Cc
        ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s, \<sigma>ls)) \<in> G\<^sub>c \<and> ((s,\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls))\<in> \<xi>\<^sub>1}), {}" using a10 by auto
  have step_s:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (S,  (\<Sigma>g,\<Sigma>l))" by auto
  moreover have g_s:"(((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> G\<^sub>s\<^sup>*"  by auto  
  obtain cc' where step_Cc:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Await b Cc \<tau>, (\<sigma>g,\<sigma>l)) \<rightarrow> (cc', (\<sigma>g',\<sigma>l'))" and 
                   cc':"c\<^sub>c' = LanguageCon.com.Seq cc' C2" 
    using stepc_elim_cases1(7)[OF a3, simplified a9] by auto 
  then have step: "(cc' = Skip \<and> \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc, Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Normal (\<sigma>g',\<sigma>l')) \<or>
                   (cc' = Throw \<and> \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Abrupt  (\<sigma>g',\<sigma>l')) \<or> 
                   (cc' = Stuck \<and> \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Semantic.Stuck ) \<or> 
                   (\<exists>f. cc' = Fault f \<and> \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Semantic.Fault f)" and 
               \<sigma>b:"(\<sigma>g,\<sigma>l)\<in>b"
    using stepc_elim_casese[OF step_Cc]
    by (auto intro:stepc_elim_casese[OF step_Cc])
  moreover {
    assume a00:"cc' = Skip"
    then have "\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Normal (\<sigma>g',\<sigma>l')" using step by auto  
    then have "(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls)) \<in> G\<^sub>c \<and> (((\<sigma>g',\<sigma>l'),\<sigma>ls),  ((\<Sigma>g,\<Sigma>l),\<Sigma>ls))\<in> \<xi>\<^sub>1"
      using step_imp_normal_rel_ hoare a2 \<sigma>b by fast
    moreover have "(\<Gamma>\<^sub>c,(c\<^sub>c',((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S,  ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
      using Impl_Seq_Skip_sim[OF a0' a1 a4  a8] calculation a00 cc' 
      unfolding RGSim_pre_def by auto
    ultimately have ?thesis using step_s g_s a0' a0 a2
      unfolding related_transitions_def by fast
  }
  moreover {
    assume "cc' = Throw \<or> (\<exists>f. cc' = Fault f) \<or> (cc' = Stuck)" 
    then obtain \<sigma>' where s:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> \<sigma>'" and 
                         n:"\<forall>\<sigma>n. \<sigma>' \<noteq> Normal \<sigma>n" using step by auto    
    then have ?thesis using a7 a2 \<sigma>b  by (auto intro: not_normal_false[OF hoare s n _]) 
  }                                
  ultimately show ?thesis  by auto        
qed


lemma imp_seq_await_sim: 
  assumes
 a1:"\<xi> \<subseteq> \<alpha>" and  a2:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and  
 a9:"C1 = Await b Cc \<tau>" and   
  a10:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
        (b \<inter> {s. (\<sigma>g,\<sigma>l) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Cc
        ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s, \<sigma>ls)) \<in> G\<^sub>c \<and> ((s,\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls))\<in> \<xi>\<^sub>1}), {}"  and
 a7:"\<forall>\<sigma>g \<sigma>l. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal  (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Semantic.Fault f"  and
 a12:"(\<Gamma>\<^sub>c,C2,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)" 
shows "(\<Gamma>\<^sub>c,Seq C1 C2 ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)"  
  
proof-
  { fix \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls 
    assume "(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" 
    then have "(\<Gamma>\<^sub>c,(Seq C1 C2, ((\<sigma>g,\<sigma>l),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
      apply (coinduction arbitrary: \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls)
      apply clarsimp
      apply (rule conjId)+  
      apply (rule, rule, rule, rule, rule, rule, rule)
         apply (meson a3 sim_env)
        apply (rule, rule, rule, rule, rule)
      unfolding toSeq_def apply auto[1]
        apply (frule mod_state_tran_v;  insert a9, fastforce+)
      apply(rule, rule, rule, rule) apply (simp add: fst_def) 
        apply (frule mod_state_only_atomic_sound2[OF a1 a2 a4 _ _ a9 a6 a12 a10 a7] , auto)
      using  a1 by auto   
  } then show ?thesis unfolding RGSim_pre_def by auto
qed

lemma Spec_Seq_Skip_sim: assumes a0:"\<xi> \<subseteq> \<alpha>" and 
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and  
 a8: "(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)" 
shows "(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,Seq Skip S,R\<^sub>s,G\<^sub>s)"  
proof-
  {fix \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls
    
  assume a11: "(((\<sigma>g, \<sigma>l), \<sigma>ls), (\<Sigma>g, \<Sigma>l), \<Sigma>ls) \<in> \<xi>"   
  then have "(\<Gamma>\<^sub>c,(C,((\<sigma>g, \<sigma>l), \<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S, (\<Sigma>g, \<Sigma>l), \<Sigma>ls),R\<^sub>s,G\<^sub>s)"
  proof(coinduction arbitrary:  \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls,simp)    
  { fix  \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls
    let ?\<sigma>s = "(\<sigma>g, \<sigma>l)::('a \<times> 'b)"  and 
        ?\<Sigma>s = "(\<Sigma>g,\<Sigma>l)::('c \<times> 'd)"  
    let ?\<sigma> = "(?\<sigma>s,\<sigma>ls)::(('a \<times> 'b) \<times> 'b list)" and 
        ?\<Sigma> = "(?\<Sigma>s,\<Sigma>ls)::(('c \<times> 'd) \<times> 'd list)"    
    assume a11:"(?\<sigma>, ?\<Sigma>) \<in> \<xi>"  
    have x:"(\<Gamma>\<^sub>c,(C, ?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, ?\<Sigma>),R\<^sub>s,G\<^sub>s)" 
      using a8 a11 unfolding RGSim_pre_def by auto  
    have step_s:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq Skip S, ?\<Sigma>s) \<rightarrow> (S, ?\<Sigma>s)"
      using SeqSkipc by fast
    then have step_s1:
      "\<forall>S' \<Sigma>'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, ?\<Sigma>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (S', \<Sigma>') \<longrightarrow> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Skip S, ?\<Sigma>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (S', \<Sigma>')"
      by auto
    have "(?\<sigma>, ?\<Sigma>) \<in> \<alpha>" using a11 a0 by auto
    moreover have "\<forall>c\<^sub>c' a b.
         \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (C, CRef.toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', CRef.toSeq ((a, b),  \<sigma>ls)) \<longrightarrow>
         (\<exists>c\<^sub>s' aa ba.
             \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', CRef.toSeq ((aa, ba),  \<Sigma>ls)) \<and>
             (((a, b), snd ((\<sigma>g, \<sigma>l), \<sigma>ls)), (aa, ba), snd ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<in> \<alpha> \<and>
             ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
             (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba),  \<Sigma>ls),R\<^sub>s,G\<^sub>s))"
      by (auto intro: sim_elim_cases[OF x])
    then have "\<forall>c\<^sub>c' a b.
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (C, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((a, b), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Skip S, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((aa, ba), \<Sigma>ls)) \<and>
                (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                (c\<^sub>c' = C \<and> c\<^sub>s' = Seq Skip S \<and> (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or> 
                  (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))"  
      unfolding toSeq_def apply auto using step_s1  by fast    
  moreover have "\<forall>v c\<^sub>c' a b.
     \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((a, b),  \<sigma>ls)) \<longrightarrow>
     (\<exists>c\<^sub>s' aa ba.
         (\<exists>a ab b.
             \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
             (\<exists>ac ad bb.
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, ab, b) \<rightarrow> (ac, ad, bb) \<and>
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ac, ad, bb) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', CRef.toSeq ((aa, ba), \<Sigma>ls)))) \<and>
         (((a, b), snd ((\<sigma>g, \<sigma>l), \<sigma>ls)), (aa, ba),\<Sigma>ls) \<in> \<alpha> \<and>
         ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
         (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s))" 
    by (fastforce intro: sim_elim_cases[OF x]) 
  then have "\<forall>v c\<^sub>c' a b.
     \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((a, b),  \<sigma>ls)) \<longrightarrow>
     (\<exists>c\<^sub>s' aa ba.
         \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (Seq Skip S, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sup>+  (c\<^sub>s',CRef.toSeq ((aa, ba), \<Sigma>ls)) \<and>
         (((a, b), snd ((\<sigma>g, \<sigma>l), \<sigma>ls)), (aa, ba),\<Sigma>ls) \<in> \<alpha> \<and>
         ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
         (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s))"   
    using event_tran_closure_tau_tran[OF step_s] 
    unfolding toSeq_def apply auto by (meson)
  then have "\<forall>v c\<^sub>c' a b.
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((a, b), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                (\<exists>a ab b.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Skip S, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                    (\<exists>ac ad bb. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, ab, b) \<rightarrow> (ac, ad, bb) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ac, ad, bb) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((aa, ba), \<Sigma>ls)))) \<and>
                (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                (c\<^sub>c' = C \<and> c\<^sub>s' = Seq Skip S \<and> 
               (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or> (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c)
                 \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))" by fastforce
  moreover {
    fix a b ba aa bb bc 
    assume a00:"((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), ba), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, bb), bc) \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>"   
    have " (((a, b), ba), (aa, bb), bc) \<in> \<xi> \<or> (\<Gamma>\<^sub>c,(C, (a, b), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
            (\<Gamma>\<^sub>s,(LanguageCon.com.Seq LanguageCon.com.Skip S, (aa, bb), bc),R\<^sub>s,G\<^sub>s)"
      using sim_env[OF  a11 a3   a00] by blast
  }
  moreover have 
     "(C = LanguageCon.com.Skip \<longrightarrow>
       (\<exists>a b. ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (a, b), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                (((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<Sigma>ls) \<in> \<gamma>\<^sub>n \<and>\<gamma>\<^sub>n \<subseteq> \<alpha> \<and>
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Skip S, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, toSeq ((a, b), \<Sigma>ls))))"
    using sim_elim_cases[OF x] unfolding toSeq_def apply auto
    using step_s converse_rtranclp_into_rtranclp by smt    
  moreover have 
    "C = LanguageCon.com.Throw \<longrightarrow>
     (\<exists>a b. ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (a, b), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                (((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<Sigma>ls) \<in> \<gamma>\<^sub>a \<and> \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Skip S, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>*  (Throw, toSeq ((a, b), \<Sigma>ls)))"
    using sim_elim_cases[OF x] unfolding toSeq_def apply auto 
    using step_s converse_rtranclp_into_rtranclp by smt
  moreover have 
    "(\<forall>f. C = com.Fault f \<longrightarrow>
     (\<exists>a b. ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (a, b), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
      \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Skip S, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, toSeq ((a, b), \<Sigma>ls)) \<and>
      (((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<Sigma>ls) \<in> \<alpha>))"
    using sim_elim_cases[OF x] unfolding toSeq_def apply auto 
    using step_s converse_rtranclp_into_rtranclp by smt
  moreover have 
    "(C = com.Stuck \<longrightarrow>
       (\<exists>a b. ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (a, b), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Skip S, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, toSeq ((a, b), \<Sigma>ls)) \<and>
                (((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<Sigma>ls) \<in> \<alpha>))" 
    using sim_elim_cases[OF x] unfolding toSeq_def apply auto 
    using step_s converse_rtranclp_into_rtranclp by smt 
   ultimately show 
      "(((\<sigma>g, \<sigma>l), \<sigma>ls), (\<Sigma>g, \<Sigma>l), \<Sigma>ls) \<in> \<alpha> \<and>
           (\<forall>c\<^sub>c' a b.
               \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (C, CRef.toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', CRef.toSeq ((a, b), \<sigma>ls)) \<longrightarrow>
               (\<exists>c\<^sub>s' aa ba.
                   \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq LanguageCon.com.Skip S, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                           (c\<^sub>s', CRef.toSeq ((aa, ba), \<Sigma>ls)) \<and>
                   (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                   ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                   (c\<^sub>c' = C \<and>
                    c\<^sub>s' = LanguageCon.com.Seq LanguageCon.com.Skip S \<and> (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or>
                    (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))) \<and>
           (\<forall>v c\<^sub>c' a b.
               \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C, CRef.toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', CRef.toSeq ((a, b), \<sigma>ls)) \<longrightarrow>
               (\<exists>c\<^sub>s' aa ba.
                   (\<exists>a ab b.
                       \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq LanguageCon.com.Skip S, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                               (a, ab, b) \<and>
                       (\<exists>ac ad bb.
                           \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, ab, b) \<rightarrow> (ac, ad, bb) \<and>
                           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ac, ad, bb) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', CRef.toSeq ((aa, ba), \<Sigma>ls)))) \<and>
                   (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                   ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                   (c\<^sub>c' = C \<and>
                    c\<^sub>s' = LanguageCon.com.Seq LanguageCon.com.Skip S \<and> (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or>
                    (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))) \<and>
           (\<forall>a b ba aa bb bc.
               ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), ba), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, bb), bc) \<in> ((R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<longrightarrow>
               (((a, b), ba), (aa, bb), bc) \<in> \<xi> \<or> (\<Gamma>\<^sub>c,(C, (a, b), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)
               (\<Gamma>\<^sub>s,(LanguageCon.com.Seq LanguageCon.com.Skip S, (aa, bb), bc),R\<^sub>s,G\<^sub>s)) \<and>
           (C = LanguageCon.com.Skip \<longrightarrow>
            (\<exists>a b. ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (a, b), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                   (((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<Sigma>ls) \<in> \<gamma>\<^sub>n \<and>
                   \<gamma>\<^sub>n \<subseteq> \<alpha> \<and>
                   \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq LanguageCon.com.Skip S, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                           (LanguageCon.com.Skip, CRef.toSeq ((a, b), \<Sigma>ls)))) \<and>
           (C = LanguageCon.com.Throw \<longrightarrow>
            (\<exists>a b. ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (a, b), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                   (((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<Sigma>ls) \<in> \<gamma>\<^sub>a \<and>
                   \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
                   \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq LanguageCon.com.Skip S, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                           (LanguageCon.com.Throw, CRef.toSeq ((a, b), \<Sigma>ls)))) \<and>
           (\<forall>f. C = com.Fault f \<longrightarrow>
                (\<exists>a b. ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (a, b), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                       \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq LanguageCon.com.Skip S, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                               (com.Fault f, CRef.toSeq ((a, b), \<Sigma>ls)) \<and>
                       (((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<Sigma>ls) \<in> \<alpha>)) \<and>
           (C = com.Stuck \<longrightarrow>
            (\<exists>a b. ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (a, b), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                   \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq LanguageCon.com.Skip S, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>*
                           (com.Stuck, CRef.toSeq ((a, b), \<Sigma>ls)) \<and>
                   (((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<Sigma>ls) \<in> \<alpha>))"
     by blast
 } qed
} thus ?thesis unfolding RGSim_pre_def by auto
qed

  
lemma Spec_Seq_Throw_sim: assumes a0:"\<xi> \<subseteq> \<alpha>" and 
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" 
shows "(\<Gamma>\<^sub>c,Throw,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>) (\<Gamma>\<^sub>s,Seq Throw S,R\<^sub>s,G\<^sub>s)"
proof-
{fix  \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls
  assume a11: "(((\<sigma>g, \<sigma>l), \<sigma>ls), (\<Sigma>g, \<Sigma>l), \<Sigma>ls) \<in> \<xi>"   
  then have "(\<Gamma>\<^sub>c,(Throw, ((\<sigma>g, \<sigma>l), \<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>) (\<Gamma>\<^sub>s,(Seq Throw S, (\<Sigma>g, \<Sigma>l), \<Sigma>ls),R\<^sub>s,G\<^sub>s)" 
  proof (coinduction arbitrary: \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls,simp)  
  {fix  \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls
    let ?\<sigma>s = "(\<sigma>g, \<sigma>l)::('a \<times> 'b)"  and 
        ?\<Sigma>s = "(\<Sigma>g,\<Sigma>l)::('c \<times> 'd)"  
    let ?\<sigma> = "(?\<sigma>s,\<sigma>ls)::(('a \<times> 'b) \<times> 'b list)" and 
        ?\<Sigma> = "(?\<Sigma>s,\<Sigma>ls)::(('c \<times> 'd) \<times> 'd list)"    
    assume a11:"(?\<sigma>, ?\<Sigma>) \<in> \<xi>"  
    have x:"(\<Gamma>\<^sub>c,(Throw, ?\<sigma>),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>) (\<Gamma>\<^sub>s,(Throw,  ?\<Sigma>),R\<^sub>s,G\<^sub>s)"
      using Throw_sound[OF a0 a3 a6 ] a11 unfolding RGSim_pre_def by fastforce  
    have step_s:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq Throw S, ?\<Sigma>s) \<rightarrow> (Throw, ?\<Sigma>s)"
      using SeqThrowc by fastforce
    then have step_s1:
      "\<forall>S' \<Sigma>'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Throw, ?\<Sigma>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (S', \<Sigma>') \<longrightarrow> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Throw S, ?\<Sigma>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (S', \<Sigma>')"
      by auto
    moreover have "(?\<sigma>, ?\<Sigma>) \<in> \<alpha> " using a11 a0 by auto
    moreover have "\<forall>c\<^sub>c' a b.
         \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Throw, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((a, b),  \<sigma>ls)) \<longrightarrow>
         (\<exists>c\<^sub>s' aa ba.
             \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Throw, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((aa, ba),  \<Sigma>ls)) \<and>
             (((a, b), snd ((\<sigma>g, \<sigma>l), \<sigma>ls)), (aa, ba), snd ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<in> \<alpha> \<and>
             ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
             (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba),  \<Sigma>ls),R\<^sub>s,G\<^sub>s))"     
      by (auto intro: sim_elim_cases[OF x])
    then have 
      "\<forall>c\<^sub>c' a b.
               \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Throw, CRef.toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', CRef.toSeq ((a, b),  \<sigma>ls)) \<longrightarrow>
               (\<exists>c\<^sub>s' aa ba.
                   \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Throw S, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((aa, ba),  \<Sigma>ls)) \<and>
                   (((a, b), snd ((\<sigma>g, \<sigma>l), \<sigma>ls)), (aa, ba), snd ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<in> \<alpha> \<and>
                   ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                    (c\<^sub>c' = Throw \<and> c\<^sub>s' = Seq LanguageCon.com.Throw S \<and> 
                     (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or>
                     (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba),  \<Sigma>ls),R\<^sub>s,G\<^sub>s)))"   
      unfolding toSeq_def  apply auto using step_s1 by fast
    moreover have "\<forall>v c\<^sub>c' a b.
      \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Throw, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((a, b),  \<sigma>ls)) \<longrightarrow>
      (\<exists>c\<^sub>s' aa ba.
         (\<exists>a ab b.
             \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Throw, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
             (\<exists>ac ad bb.
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, ab, b) \<rightarrow> (ac, ad, bb) \<and>
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ac, ad, bb) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', CRef.toSeq ((aa, ba), \<Sigma>ls)))) \<and>
         (((a, b), snd ((\<sigma>g, \<sigma>l), \<sigma>ls)), (aa, ba),\<Sigma>ls) \<in> \<alpha> \<and>
         ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
         (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s))" 
      by (fastforce intro: sim_elim_cases[OF x]) 
    then have "\<forall>v c\<^sub>c' a b.
     \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Throw, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((a, b),  \<sigma>ls)) \<longrightarrow>
     (\<exists>c\<^sub>s' aa ba.
         \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>v (Seq Throw S, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sup>+  (c\<^sub>s',CRef.toSeq ((aa, ba), \<Sigma>ls)) \<and>
         (((a, b), snd ((\<sigma>g, \<sigma>l), \<sigma>ls)), (aa, ba),\<Sigma>ls) \<in> \<alpha> \<and>
         ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
         (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s))"   
      using event_tran_closure_tau_tran[OF step_s] 
      unfolding toSeq_def apply auto by (meson)
    then have "\<forall>v c\<^sub>c' a b.
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Throw, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((a, b), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                (\<exists>a ab b.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Throw S, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                    (\<exists>ac ad bb. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, ab, b) \<rightarrow> (ac, ad, bb) \<and> 
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ac, ad, bb) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((aa, ba), \<Sigma>ls)))) \<and>
                (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                (c\<^sub>c' = Throw \<and> c\<^sub>s' = Seq Throw S \<and> 
               (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or> (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c)
                 \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))" by fastforce
    moreover {
      fix a b ba aa bb bc 
      assume a00:"((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), ba), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, bb), bc) \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>"   
      have " (((a, b), ba), (aa, bb), bc) \<in> \<xi> \<or> (\<Gamma>\<^sub>c,(Throw, (a, b), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>)
            (\<Gamma>\<^sub>s,(Seq Throw S, (aa, bb), bc),R\<^sub>s,G\<^sub>s)"
        using sim_env[OF  a11 a3   a00] by blast
    }
    moreover have "(\<exists>a b. ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (a, b), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                (((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<Sigma>ls) \<in> \<xi> \<and> \<xi> \<subseteq> \<alpha> \<and>
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Throw S, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>*  (Throw, toSeq ((a, b), \<Sigma>ls)))"
      using sim_elim_cases[OF x] unfolding toSeq_def apply auto 
      using step_s converse_rtranclp_into_rtranclp by smt

    ultimately show 
      "(((\<sigma>g, \<sigma>l), \<sigma>ls), (\<Sigma>g, \<Sigma>l), \<Sigma>ls) \<in> \<alpha> \<and>
        (\<forall>c\<^sub>c' a b.
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Throw,toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c',  toSeq ((a, b), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Throw S, CRef.toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((aa, ba), \<Sigma>ls)) \<and>
                (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                (c\<^sub>c' = Throw \<and>
                 c\<^sub>s' = Seq Throw S \<and> (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))) \<and>
        (\<forall>v c\<^sub>c' a b.
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Throw, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((a, b), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                (\<exists>a ab b.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Throw S, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                    (\<exists>ac ad bb.
                        \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, ab, b) \<rightarrow> (ac, ad, bb) \<and>
                        \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ac, ad, bb) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((aa, ba), \<Sigma>ls)))) \<and>
                (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                (c\<^sub>c' = Throw \<and>
                 c\<^sub>s' = Seq Throw S \<and> (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))) \<and>
        (\<forall>a b ba aa bb bc.
            ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), ba), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, bb), bc) \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha> \<longrightarrow>
            (((a, b), ba), (aa, bb), bc) \<in> \<xi> \<or> 
            (\<Gamma>\<^sub>c,(Throw, (a, b), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<xi>\<^sub>) (\<Gamma>\<^sub>s,(Seq Throw S, (aa, bb), bc),R\<^sub>s,G\<^sub>s)) \<and>
        (\<exists>a b. ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (a, b), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
               (((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<Sigma>ls) \<in> \<xi> \<and>
               \<xi> \<subseteq> \<alpha> \<and>
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Throw S, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, toSeq ((a, b), \<Sigma>ls)))"
     by fastforce
 } qed
} thus ?thesis unfolding RGSim_pre_def by auto
qed


lemma spec_mod_state_only_atomic_sound2:
  assumes a0:"\<xi> \<subseteq> \<alpha> " and a0':"\<xi>\<^sub>1 \<subseteq> \<alpha> " and a1:"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and 
          a2:"(((\<sigma>g, \<sigma>l), \<sigma>ls), (\<Sigma>g, \<Sigma>l), \<Sigma>ls) \<in> \<xi>" and 
          a3:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Seq C1 C2, (\<sigma>g, \<sigma>l)) \<rightarrow> (c\<^sub>c', (\<sigma>g', \<sigma>l'))" and        
      a9:"C1 = Await b Cc \<tau>" and   
      a6:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and
      a4:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal \<sigma>\<rangle> \<Rightarrow> Semantic.Fault f" and
      a8:"(\<Gamma>\<^sub>c,C2,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)" and      
      a10:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
             (b \<inter> {s. (\<sigma>g,\<sigma>l) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Cc 
             ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s, \<sigma>ls)) \<in> G\<^sub>c} \<inter> 
              {s. ((s,\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls))\<in> \<xi>\<^sub>1}), {}"       
  shows "(\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g, \<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',(\<Sigma>g', \<Sigma>l')) \<and>
          (((\<sigma>g', \<sigma>l'), \<sigma>ls), ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<in> \<alpha> \<and>
          ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g', \<sigma>l'), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          (c\<^sub>c' = LanguageCon.com.Seq C1 C2 \<and> c\<^sub>s' = S \<and> (\<sigma>n', \<Sigma>n') \<in> \<xi> \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', ((\<sigma>g', \<sigma>l'), \<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',( (\<Sigma>g', \<Sigma>l'), \<Sigma>ls)),R\<^sub>s,G\<^sub>s)))"
proof-  
  
  have hoare:"\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^bsub>/F\<^esub> 
           (b \<inter> {s. (\<sigma>g,\<sigma>l) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Cc 
             ({s. (((\<sigma>g,\<sigma>l),\<sigma>ls), (s, \<sigma>ls)) \<in> G\<^sub>c} \<inter> 
              {s. ((s,\<sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls))\<in> \<xi>\<^sub>1}), {}" using a10 by auto    
  have step_s:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g, \<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (S, (\<Sigma>g, \<Sigma>l))" by auto
  moreover have g_s:"(((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> G\<^sub>s\<^sup>*"  by auto  
  obtain cc' where step_Cc:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Await b Cc \<tau>, (\<sigma>g, \<sigma>l)) \<rightarrow> (cc', (\<sigma>g', \<sigma>l'))" and 
                   cc':"c\<^sub>c' = Seq cc' C2" 
    using stepc_elim_cases1(7)[OF a3, simplified a9] by auto 
  then have step: "(cc' = Skip \<and> \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Normal (\<sigma>g',\<sigma>l')) \<or>
                   (cc' = Throw \<and> \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Abrupt (\<sigma>g',\<sigma>l')) \<or>
                   (cc' = Stuck \<and> \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Semantic.Stuck) \<or>
                   ((\<exists>f. cc' = Fault f \<and>  \<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Semantic.Fault f))"  
             and \<sigma>b:"(\<sigma>g,\<sigma>l)\<in>b"
    by (auto intro:stepc_elim_casese[OF step_Cc])
  moreover {
    assume a00:"cc' = Skip"
    then have "\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal  (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> Normal (\<sigma>g',\<sigma>l')" using step by auto      
    
    then have "(((\<sigma>g,\<sigma>l),\<sigma>ls), (\<sigma>g',\<sigma>l'),\<sigma>ls) \<in> G\<^sub>c \<and> (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls))\<in> \<xi>\<^sub>1"
      using step_imp_normal_rel_ hoare a2 \<sigma>b by fast 
    moreover have "(\<Gamma>\<^sub>c,(c\<^sub>c',((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S, ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
      using Impl_Seq_Skip_sim[OF a0' a1 a6  a8] calculation a00 cc' 
      unfolding RGSim_pre_def by auto
    ultimately have ?thesis using step_s g_s a0' a0 a2
      unfolding related_transitions_def by fast
  }
  moreover {
    assume "cc' = Throw \<or>  cc' = Stuck \<or> (\<exists>f. cc' = Fault f)" 
    then obtain \<sigma>' where "\<Gamma>\<^sub>c\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Cc,Normal (\<sigma>g,\<sigma>l)\<rangle> \<Rightarrow> \<sigma>' \<and> (\<forall>\<sigma>''. \<sigma>' \<noteq> Normal \<sigma>'')"  using step by auto    
    then have ?thesis using not_normal_false[OF hoare] a2 \<sigma>b a4 by blast
  }
  ultimately show ?thesis  by auto        
qed

lemma await_step_sim_cond:
  assumes 
  a0:"(((\<sigma>g, \<sigma>l), \<sigma>ls), (\<Sigma>g, \<Sigma>l), \<Sigma>ls)  \<in> \<xi>" and a2:"Range \<xi> \<subseteq> {s. fst s \<in> b}" and
  a3:"S1 = Await b Ss \<tau>"  and
  a4:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
             (b \<inter> {s. (\<Sigma>g, \<Sigma>l) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Ss 
             {s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), (s, \<Sigma>ls)) \<in> G\<^sub>s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),(s,\<Sigma>ls)) \<in> \<xi>\<^sub>1}, {}"  and
  a5:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Ss,Normal \<sigma>\<rangle> \<Rightarrow> Semantic.Fault f" 
obtains \<Sigma>g' \<Sigma>l' where "(((\<sigma>g, \<sigma>l), \<sigma>ls), (\<Sigma>g', \<Sigma>l'), \<Sigma>ls) \<in> \<xi>\<^sub>1 \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in>G\<^sub>s \<and> 
                  \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, (\<Sigma>g, \<Sigma>l)) \<rightarrow> (Skip, (\<Sigma>g', \<Sigma>l'))"  
proof-
  have "(\<Sigma>g, \<Sigma>l) \<in> b" using a0 a2 by auto
  moreover have "\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub>
                 (b \<inter> {s. (\<Sigma>g, \<Sigma>l) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Ss 
                 {s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), (s, \<Sigma>ls)) \<in> G\<^sub>s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),(s,\<Sigma>ls)) \<in> \<xi>\<^sub>1}, {}" 
    using a4 by auto
  then have "\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<Turnstile>\<^sub>t\<^bsub>/F\<^esub> 
             (b \<inter> {s. (\<Sigma>g, \<Sigma>l) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Ss 
                 {s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), (s, \<Sigma>ls)) \<in> G\<^sub>s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),(s,\<Sigma>ls)) \<in> \<xi>\<^sub>1}, {}"
    using hoaret_sound' by blast  
  moreover obtain \<Sigma>g' \<Sigma>l' where "\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Ss, Normal (\<Sigma>g,\<Sigma>l)\<rangle> \<Rightarrow> Normal (\<Sigma>g', \<Sigma>l') \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and> 
                                      (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), (\<Sigma>g',\<Sigma>l'),\<Sigma>ls)\<in>G\<^sub>s"
    using calculation a0 a5 Termination.terminates_implies_exec  unfolding validt_def valid_def
    by (fastforce dest: Termination.terminates_implies_exec)
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Skip, (\<Sigma>g',\<Sigma>l'))" 
    using a3 calculation Awaitc  by fastforce
  ultimately show ?thesis
    using that by fastforce
qed
 
lemma spec_mod_state_only_Await_sound0:
  assumes 
  a0:"(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and a0':"\<xi>\<subseteq>\<alpha>" and a1:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and a1':"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
  a2:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and  
  a6:"S1 = Await b Ss \<tau>" and a7:"Range \<xi> \<subseteq> {s. fst s \<in> b}" and
  a8:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
             (b \<inter> {s. (\<Sigma>g, \<Sigma>l) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Ss 
             {s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), (s, \<Sigma>ls)) \<in> G\<^sub>s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),(s,\<Sigma>ls)) \<in> \<xi>\<^sub>1}, {}"  and
  a9:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Ss,Normal \<sigma>\<rangle> \<Rightarrow> Semantic.Fault f" and
  a10:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" and   
  a11:"C =Stuck" shows
      "\<exists> \<Sigma>g' \<Sigma>l'. ((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g,\<sigma>l),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
              (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<alpha> \<and>
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq S1 S2,(\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, (\<Sigma>g',\<Sigma>l'))"
proof-

obtain \<Sigma>g' \<Sigma>l' where 
   sim_cond:"(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in>G\<^sub>s \<and> 
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Skip, (\<Sigma>g',\<Sigma>l'))" 
    using await_step_sim_cond[OF a0 a7 a6 a8 a9] by auto
  moreover have step:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq S1 S2,  (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Seq Skip S2, (\<Sigma>g',\<Sigma>l'))"
    using Seqc calculation by fastforce
  moreover have x:"(\<Gamma>\<^sub>c,(C,((\<sigma>g,\<sigma>l),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S2, ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
    using  calculation Spec_Seq_Skip_sim[OF a1 a1' a2  a10] 
    unfolding RGSim_pre_def by auto  
  thm sim_elim_cases_c(4)[OF x[simplified a11]]
  ultimately obtain \<Sigma>g'' \<Sigma>l'' where 
    sim:"(((((\<sigma>g,\<sigma>l),\<sigma>ls)), ((\<sigma>g,\<sigma>l),\<sigma>ls)), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq Skip S2, (\<Sigma>g',\<Sigma>l')) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, (\<Sigma>g'',\<Sigma>l''))  \<and>
         (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls)) \<in> \<alpha> "   
    using sim_elim_cases_c(4)[OF x[simplified a11]] unfolding toSeq_def  by force   
  moreover have "(((((\<sigma>g,\<sigma>l),\<sigma>ls)), ((\<sigma>g,\<sigma>l),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
    using related_transition_tran[OF subsetD[OF a0' a0]] calculation sim_cond by auto
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq S1 S2, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Stuck, (\<Sigma>g'',\<Sigma>l''))"
    using step calculation by auto
  ultimately show ?thesis by auto    
qed

lemma spec_mod_state_only_Await_sound1:
  assumes 
  a0:"(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and a0':"\<xi>\<subseteq>\<alpha>" and a1:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and a1':"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
  a2:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and  
  a6:"S1 = Await b Ss \<tau>" and a7:"Range \<xi> \<subseteq> {s. fst s \<in> b}" and
  a8:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
             (b \<inter> {s. (\<Sigma>g, \<Sigma>l) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Ss 
             {s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), (s, \<Sigma>ls)) \<in> G\<^sub>s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),(s,\<Sigma>ls)) \<in> \<xi>\<^sub>1}, {}"  and
  a9:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Ss,Normal \<sigma>\<rangle> \<Rightarrow> Semantic.Fault f" and
  a10:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" and   
  a11:"C =Fault f" shows
      "\<exists> \<Sigma>g' \<Sigma>l'. ((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g,\<sigma>l),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
              (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<alpha> \<and>
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq S1 S2,(\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, (\<Sigma>g',\<Sigma>l'))"
proof-

obtain \<Sigma>g' \<Sigma>l' where 
   sim_cond:"(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in>G\<^sub>s \<and> 
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Skip, (\<Sigma>g',\<Sigma>l'))" 
    using await_step_sim_cond[OF a0 a7 a6 a8 a9] by auto
  moreover have step:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq S1 S2,  (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Seq Skip S2, (\<Sigma>g',\<Sigma>l'))"
    using Seqc calculation by fastforce
  moreover have x:"(\<Gamma>\<^sub>c,(C,((\<sigma>g,\<sigma>l),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S2, ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
    using  calculation Spec_Seq_Skip_sim[OF a1 a1' a2  a10] 
    unfolding RGSim_pre_def by auto    
  ultimately obtain \<Sigma>g'' \<Sigma>l'' where 
    sim:"(((((\<sigma>g,\<sigma>l),\<sigma>ls)), ((\<sigma>g,\<sigma>l),\<sigma>ls)), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and> 
           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq Skip S2, (\<Sigma>g',\<Sigma>l')) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, (\<Sigma>g'',\<Sigma>l''))  \<and>
         (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls)) \<in> \<alpha> "   
    using sim_elim_cases_c(3)[OF x[simplified a11]] unfolding toSeq_def  by force   
  moreover have "(((((\<sigma>g,\<sigma>l),\<sigma>ls)), ((\<sigma>g,\<sigma>l),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
    using related_transition_tran[OF subsetD[OF a0' a0]] calculation sim_cond by auto
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq S1 S2, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, (\<Sigma>g'',\<Sigma>l''))"
    using step calculation by auto
  ultimately show ?thesis by auto    
qed


lemma spec_mod_state_only_Await_sound2:
  assumes 
  a0:"(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and a0':"\<xi>\<subseteq>\<alpha>" and a1:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and a1':"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
  a2:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and  
  a6:"S1 = Await b Ss \<tau>" and a7:"Range \<xi> \<subseteq> {s. fst s \<in> b}" and
  a8:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
             (b \<inter> {s. (\<Sigma>g, \<Sigma>l) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Ss 
             {s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), (s, \<Sigma>ls)) \<in> G\<^sub>s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),(s,\<Sigma>ls)) \<in> \<xi>\<^sub>1}, {}"  and
  a9:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Ss,Normal \<sigma>\<rangle> \<Rightarrow> Semantic.Fault f" and
  a10:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" and   
  a11:"C = LanguageCon.com.Throw" shows
      "\<exists> \<Sigma>g' \<Sigma>l'. ((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g,\<sigma>l),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
              (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<gamma>\<^sub>a \<and>
              \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq S1 S2,(\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, (\<Sigma>g',\<Sigma>l'))"
proof-

obtain \<Sigma>g' \<Sigma>l' where 
   sim_cond:"(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in>G\<^sub>s \<and> 
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Skip, (\<Sigma>g',\<Sigma>l'))" 
    using await_step_sim_cond[OF a0 a7 a6 a8 a9] by auto
  moreover have step:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq S1 S2,  (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Seq Skip S2, (\<Sigma>g',\<Sigma>l'))"
    using Seqc calculation by fastforce
  moreover have x:"(\<Gamma>\<^sub>c,(C,((\<sigma>g,\<sigma>l),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S2, ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
    using  calculation Spec_Seq_Skip_sim[OF a1 a1' a2  a10] 
    unfolding RGSim_pre_def by auto  
  thm sim_elim_cases_c(2)[OF x[simplified a11]]
  ultimately obtain \<Sigma>g'' \<Sigma>l'' where 
    sim:"(((((\<sigma>g,\<sigma>l),\<sigma>ls)), ((\<sigma>g,\<sigma>l),\<sigma>ls)), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
         (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls)) \<in> \<gamma>\<^sub>a \<and> \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq Skip S2, (\<Sigma>g',\<Sigma>l')) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Throw, (\<Sigma>g'',\<Sigma>l''))"   
    using sim_elim_cases_c(2)[OF x[simplified a11]] unfolding toSeq_def  by force   
  moreover have "(((((\<sigma>g,\<sigma>l),\<sigma>ls)), ((\<sigma>g,\<sigma>l),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
    using related_transition_tran[OF subsetD[OF a0' a0]] calculation sim_cond by auto
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq S1 S2, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Throw, (\<Sigma>g'',\<Sigma>l''))"
    using step calculation by auto
  ultimately show ?thesis by auto    
qed

lemma spec_mod_state_only_Await_sound3:
  assumes 
  a0:"(((\<sigma>g, \<sigma>l), \<sigma>ls), (\<Sigma>g, \<Sigma>l), \<Sigma>ls)  \<in> \<xi>" and a0':"\<xi>\<subseteq>\<alpha>" and a1:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and 
  a1':"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a2:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and    
  a6:"S1 = Await b Ss \<tau>" and a7:"Range \<xi> \<subseteq> {s. fst s \<in> b}" and
  a8:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
             (b \<inter> {s. (\<Sigma>g, \<Sigma>l) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Ss 
             {s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), (s, \<Sigma>ls)) \<in> G\<^sub>s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),(s,\<Sigma>ls)) \<in> \<xi>\<^sub>1}, {}" and
  a9:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Ss,Normal \<sigma>\<rangle> \<Rightarrow> Semantic.Fault f" and
  a10:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" and   
  a11:"C = Skip" 
  shows
    "\<exists>\<Sigma>g' \<Sigma>l'. 
      ((((\<sigma>g, \<sigma>l), \<sigma>ls), ((\<sigma>g, \<sigma>l), \<sigma>ls)), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
      (((\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<in> \<gamma>\<^sub>n \<and> \<gamma>\<^sub>n \<subseteq> \<alpha> \<and> 
      \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq S1 S2, (\<Sigma>g, \<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, (\<Sigma>g', \<Sigma>l'))"
proof-

obtain \<Sigma>g' \<Sigma>l' where 
   sim_cond:"(((\<sigma>g, \<sigma>l), \<sigma>ls), ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and> 
             (((\<Sigma>g, \<Sigma>l), \<Sigma>ls),((\<Sigma>g', \<Sigma>l'), \<Sigma>ls))\<in>G\<^sub>s \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, (\<Sigma>g, \<Sigma>l)) \<rightarrow> (Skip, (\<Sigma>g', \<Sigma>l'))" 
    using await_step_sim_cond[OF a0 a7 a6 a8 a9] by auto
  moreover have step:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq S1 S2, (\<Sigma>g, \<Sigma>l)) \<rightarrow> (Seq Skip S2, (\<Sigma>g', \<Sigma>l'))"
    using Seqc calculation by fastforce
  moreover have x:"(\<Gamma>\<^sub>c,(C, ((\<sigma>g, \<sigma>l), \<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S2, ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
    using  calculation Spec_Seq_Skip_sim[OF a1 a1' a2  a10] 
    unfolding RGSim_pre_def by auto  
  ultimately obtain \<Sigma>g'' \<Sigma>l'' where 
    sim:"(((((\<sigma>g,\<sigma>l),\<sigma>ls)), ((\<sigma>g,\<sigma>l),\<sigma>ls)), (((\<Sigma>g',\<Sigma>l'),\<Sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls))) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
         (((\<sigma>g, \<sigma>l), \<sigma>ls), (\<Sigma>g'', \<Sigma>l''), \<Sigma>ls) \<in> \<gamma>\<^sub>n \<and> \<gamma>\<^sub>n \<subseteq> \<alpha> \<and> 
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Skip S2, (\<Sigma>g', \<Sigma>l')) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, (\<Sigma>g'', \<Sigma>l''))"   
    using sim_elim_cases_c(1)[OF x[simplified a11]] unfolding toSeq_def by force   
  moreover have "(((((\<sigma>g,\<sigma>l),\<sigma>ls)), ((\<sigma>g,\<sigma>l),\<sigma>ls)), (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls))) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
    using related_transition_tran[OF subsetD[OF a0' a0]] calculation sim_cond by auto
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq S1 S2, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, (\<Sigma>g'',\<Sigma>l''))"
    using step calculation by auto
  ultimately show ?thesis by auto    
qed

lemma spec_mod_state_only_Await_sound4: assumes 
  a0:"(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and a0':"\<xi>\<subseteq>\<alpha>" and a1:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and a1':"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
  a2:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and  
  a6:"S1 = Await b Ss \<tau>" and a7:"Range \<xi> \<subseteq> {s. fst s \<in> b}" and
  a8:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
             (b \<inter> {s. (\<Sigma>g, \<Sigma>l) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Ss 
             {s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), (s, \<Sigma>ls)) \<in> G\<^sub>s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),(s,\<Sigma>ls)) \<in> \<xi>\<^sub>1}, {}"  and
  a9:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Ss,Normal \<sigma>\<rangle> \<Rightarrow> Semantic.Fault f" and
  a10:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" and   
  a11:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C, (\<sigma>g,\<sigma>l)) \<rightarrow> (c\<^sub>c', (\<sigma>g',\<sigma>l'))"
  shows  "\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
          (\<exists>a b c. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq S1 S2, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, (b, c)) \<and>
                 (\<exists>aa ba ca. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, (b,c)) \<rightarrow> (aa, (ba,ca)) \<and>
                  \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, (ba,ca)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', (\<Sigma>g',\<Sigma>l')))) \<and>
          (((\<sigma>g',\<sigma>l'),\<sigma>ls), (\<Sigma>g',\<Sigma>l'),\<Sigma>ls) \<in> \<alpha> \<and>
          ((((\<sigma>g, \<sigma>l), \<sigma>ls), ((\<sigma>g', \<sigma>l'), \<sigma>ls)), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          (c\<^sub>c' = C \<and> c\<^sub>s' = LanguageCon.com.Seq S1 S2 \<and> (((\<sigma>g',\<sigma>l'),\<sigma>ls), (\<Sigma>g',\<Sigma>l'),\<Sigma>ls) \<in> \<xi> \<or> 
          (\<Gamma>\<^sub>c,(c\<^sub>c', ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)),R\<^sub>s,G\<^sub>s))"
proof-
 obtain \<Sigma>g' \<Sigma>l' where 
   sim_cond:"(((\<sigma>g,\<sigma>l),\<sigma>ls), (\<Sigma>g',\<Sigma>l'),\<Sigma>ls) \<in> \<xi>\<^sub>1 \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), (\<Sigma>g',\<Sigma>l'),\<Sigma>ls)\<in>G\<^sub>s \<and> 
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Skip, (\<Sigma>g',\<Sigma>l'))" 
    using await_step_sim_cond[OF a0 a7 a6 a8 a9] by auto
  moreover have u:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq S1 S2, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Seq Skip S2, (\<Sigma>g',\<Sigma>l'))"
    using Seqc calculation by fastforce
  then have x:"(\<Gamma>\<^sub>c,(C,((\<sigma>g,\<sigma>l),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S2, ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
    using  sim_cond Spec_Seq_Skip_sim[OF a1 a1' a2  a10] 
    unfolding RGSim_pre_def by auto  
  moreover obtain c\<^sub>s' \<Sigma>g'' \<Sigma>l'' where 
    "(\<exists>a ab b.
           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq LanguageCon.com.Skip S2, \<Sigma>g', \<Sigma>l') \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
           (\<exists>ac ad bb.
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, ab, b) \<rightarrow> (ac, ad, bb) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ac, ad, bb) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', (\<Sigma>g'', \<Sigma>l'')))) \<and>
       (((\<sigma>g', \<sigma>l'), \<sigma>ls), (\<Sigma>g'', \<Sigma>l''), \<Sigma>ls) \<in> \<alpha> \<and>
       ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g', \<sigma>l'), \<sigma>ls), ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls), (\<Sigma>g'', \<Sigma>l''), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
       (\<Gamma>\<^sub>c,(c\<^sub>c', (\<sigma>g', \<sigma>l'), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (\<Sigma>g'', \<Sigma>l''), \<Sigma>ls),R\<^sub>s,G\<^sub>s)" 
    apply (rule sim_elim_cases[OF x]) using a11 unfolding toSeq_def by force
  then have "(\<exists>a ab b.
           \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq S1 S2, \<Sigma>g, \<Sigma>l) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
           (\<exists>ac ad bb.
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (a, ab, b) \<rightarrow> (ac, ad, bb) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ac, ad, bb) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', (\<Sigma>g'', \<Sigma>l'')))) \<and>
       (((\<sigma>g', \<sigma>l'), \<sigma>ls), (\<Sigma>g'', \<Sigma>l''), \<Sigma>ls) \<in> \<alpha> \<and>
       ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g', \<sigma>l'), \<sigma>ls), ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls), (\<Sigma>g'', \<Sigma>l''), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
       (\<Gamma>\<^sub>c,(c\<^sub>c', (\<sigma>g', \<sigma>l'), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (\<Sigma>g'', \<Sigma>l''), \<Sigma>ls),R\<^sub>s,G\<^sub>s)"
    using u by (metis (no_types, lifting) converse_rtranclp_into_rtranclp)
  moreover have "((((\<sigma>g, \<sigma>l), \<sigma>ls),((\<sigma>g', \<sigma>l'), \<sigma>ls)), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), ((\<Sigma>g'', \<Sigma>l''), \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
    using related_transition_tran[OF subsetD[OF a0' a0]] calculation sim_cond 
    by auto
  ultimately show ?thesis by fast
qed

lemma spec_mod_state_only_Await_sound5: assumes 
   a0:"(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and a0':"\<xi>\<subseteq>\<alpha>" and a1:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and a1':"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
  a2:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and  
  a6:"S1 = Await b Ss \<tau>" and a7:"Range \<xi> \<subseteq> {s. fst s \<in> b}" and
  a8:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
             (b \<inter> {s. (\<Sigma>g, \<Sigma>l) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Ss 
             {s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), (s, \<Sigma>ls)) \<in> G\<^sub>s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),(s,\<Sigma>ls)) \<in> \<xi>\<^sub>1}, {}"  and
  a9:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Ss,Normal \<sigma>\<rangle> \<Rightarrow> Semantic.Fault f" and
  a10:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" and   
  a11:" \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (C, (\<sigma>g,\<sigma>l)) \<rightarrow> (c\<^sub>c', (\<sigma>g',\<sigma>l'))"
  shows  "\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq S1 S2, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',(\<Sigma>g',\<Sigma>l')) \<and>
            (((\<sigma>g',\<sigma>l'),\<sigma>ls), (\<Sigma>g',\<Sigma>l'),\<Sigma>ls) \<in> \<alpha> \<and>
          ((((\<sigma>g, \<sigma>l), \<sigma>ls), ((\<sigma>g', \<sigma>l'), \<sigma>ls)), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          (c\<^sub>c' = C \<and> c\<^sub>s' = LanguageCon.com.Seq S1 S2 \<and> (((\<sigma>g',\<sigma>l'),\<sigma>ls), (\<Sigma>g',\<Sigma>l'),\<Sigma>ls) \<in> \<xi> \<or> 
          (\<Gamma>\<^sub>c,(c\<^sub>c', ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',((\<Sigma>g', \<Sigma>l'), \<Sigma>ls)),R\<^sub>s,G\<^sub>s))"
proof-
 obtain \<Sigma>g' \<Sigma>l' where 
   sim_cond:"(((\<sigma>g,\<sigma>l),\<sigma>ls), (\<Sigma>g',\<Sigma>l'),\<Sigma>ls) \<in> \<xi>\<^sub>1 \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), (\<Sigma>g',\<Sigma>l'),\<Sigma>ls)\<in>G\<^sub>s \<and> 
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Skip, (\<Sigma>g',\<Sigma>l'))" 
    using await_step_sim_cond[OF a0 a7 a6 a8 a9] by auto
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq S1 S2, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Seq Skip S2, (\<Sigma>g',\<Sigma>l'))"
    using Seqc calculation by fastforce
  moreover have x:"(\<Gamma>\<^sub>c,(C,((\<sigma>g,\<sigma>l),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S2, ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
    using  calculation Spec_Seq_Skip_sim[OF a1 a1' a2  a10] 
    unfolding RGSim_pre_def by auto  
  moreover obtain c\<^sub>s'  \<Sigma>g'' \<Sigma>l'' where 
        "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Skip S2,  (\<Sigma>g',\<Sigma>l')) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', (\<Sigma>g'',\<Sigma>l'')) \<and>
         (((\<sigma>g', \<sigma>l'), \<sigma>ls), (\<Sigma>g'', \<Sigma>l''), \<Sigma>ls) \<in> \<alpha> \<and>
       ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g', \<sigma>l'), \<sigma>ls), ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls), (\<Sigma>g'', \<Sigma>l''), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
       (\<Gamma>\<^sub>c,(c\<^sub>c', (\<sigma>g', \<sigma>l'), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (\<Sigma>g'', \<Sigma>l''), \<Sigma>ls),R\<^sub>s,G\<^sub>s)" 
   apply (rule sim_elim_cases[OF x]) using a11 unfolding toSeq_def by force
  moreover have "((((\<sigma>g, \<sigma>l), \<sigma>ls),((\<sigma>g', \<sigma>l'), \<sigma>ls)), 
                 ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), ((\<Sigma>g'', \<Sigma>l''), \<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
    using related_transition_tran[OF subsetD[OF a0' a0]] calculation sim_cond 
    by auto
  ultimately show ?thesis 
    by (metis (no_types, lifting) converse_rtranclp_into_rtranclp)
qed

lemma seq_await_spec_sim: 
  assumes
 a1:"\<xi> \<subseteq> \<alpha>" and  a2:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a6:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and 
 a9:"S1 = Await b Ss \<tau>" and a9':"Range \<xi> \<subseteq> {s. fst s \<in> b}" and 
 a10:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls. \<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a,{}\<turnstile>\<^sub>t\<^bsub>/F\<^esub> 
             (b \<inter> {s. (\<Sigma>g, \<Sigma>l) = s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>}) Ss 
             {s. (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), (s, \<Sigma>ls)) \<in> G\<^sub>s \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),(s,\<Sigma>ls)) \<in> \<xi>\<^sub>1}, {}" and
 a11:"\<forall>\<sigma>. \<forall>f \<in> F. \<not>\<Gamma>\<^sub>s\<^sub>\<not>\<^sub>a\<turnstile>\<langle>Ss,Normal \<sigma>\<rangle> \<Rightarrow> Semantic.Fault f" and
 a12:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" 
shows "(\<Gamma>\<^sub>c,C ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,Seq S1 S2,R\<^sub>s,G\<^sub>s)"    
proof-
  {fix  \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls
    assume "(((\<sigma>g, \<sigma>l), \<sigma>ls), (\<Sigma>g, \<Sigma>l), \<Sigma>ls) \<in> \<xi>"    
    then have "(\<Gamma>\<^sub>c,(C, ((\<sigma>g, \<sigma>l), \<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq S1 S2, ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
      apply (coinduction arbitrary: \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls)
      apply clarsimp
      apply (rule conjId)+
             apply (auto simp add: toSeq_def)[1]
             apply (frule  spec_mod_state_only_Await_sound0[OF  _ a1 a2 a4 a6   a9 a9' a10 a11 a12], fastforce+) 
            apply (auto simp add: toSeq_def)[1]
            apply (frule  spec_mod_state_only_Await_sound1[OF  _ a1 a2 a4 a6   a9 a9' a10 a11 a12], fastforce+)
           apply (auto simp add: toSeq_def)[1]
           apply (frule spec_mod_state_only_Await_sound2[OF _ a1 a2 a4 a6   a9 a9' a10 a11 a12], fastforce+)
                 apply (auto simp add: toSeq_def)[1]
          apply (frule spec_mod_state_only_Await_sound3[OF _ a1 a2 a4 a6   a9 a9' a10 a11 a12], fast+)               
      apply (meson a3 sim_env)  apply (auto simp add: toSeq_def)[1]
        apply (frule spec_mod_state_only_Await_sound4[OF _ a1 a2 a4 a6   a9 a9' a10 a11 a12], fastforce+)
       apply (auto simp add: toSeq_def)[1]
      apply (frule spec_mod_state_only_Await_sound5[OF _ a1 a2 a4 a6   a9 a9' a10 a11 a12], fast+)
      using  a1 by auto   
  } then show ?thesis unfolding RGSim_pre_def by auto
qed

lemma mod_state_tran_v_spec: "label C1 = \<tau> \<Longrightarrow>        
       \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Seq C1 C2, (\<sigma>g,\<sigma>l)) \<rightarrow> (c\<^sub>c', (\<sigma>g',\<sigma>l')) \<Longrightarrow>
       \<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
          (\<exists>a b c. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, (b,c)) \<and>
                 (\<exists>aa ba ca. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, (b,ba)) \<rightarrow> (aa, (ba,ca)) \<and> 
                  \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, (ba,ca)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', (\<Sigma>g',\<Sigma>l')))) \<and>
          (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls')) \<in> \<alpha> \<and>
          ((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
          (c\<^sub>c' = Seq C1 C2 \<and> c\<^sub>s' = S \<and> 
          (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls')) \<in> \<xi> \<or> 
            (\<Gamma>\<^sub>c,(c\<^sub>c', ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',((\<Sigma>g',\<Sigma>l'),\<Sigma>ls')),R\<^sub>s,G\<^sub>s))"
proof -
 assume a1: "\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (LanguageCon.com.Seq C1 C2, (\<sigma>g,\<sigma>l)) \<rightarrow> (c\<^sub>c', (\<sigma>g',\<sigma>l'))"
  assume a2: "label C1 = \<tau>"
  obtain c1' where s:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C1,  (\<sigma>g,\<sigma>l)) \<rightarrow> (c1',  (\<sigma>g',\<sigma>l'))" 
    using stepc_elim_cases1(7)[OF a1] by fastforce    
  thus ?thesis using label_step[OF _ s] a2 by force 
qed

lemma mod_state_only_impl_basic_tau_sound2:
  assumes a0:"\<xi> \<subseteq> \<alpha> " and a0':"\<xi>\<^sub>1 \<subseteq> \<alpha> " and a1:"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and 
          a2:"(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and 
       a3:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<sigma>g' \<sigma>l' \<Sigma>g \<Sigma>l \<Sigma>ls C. 
             (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls))\<in>\<xi> \<and> (C, (\<sigma>g',\<sigma>l')) \<in> com_step  C1 (\<sigma>g,\<sigma>l)  \<Gamma>\<^sub>c  \<longrightarrow> 
              C = Skip \<and> (((\<sigma>g',\<sigma>l'),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls))\<in>\<xi>\<^sub>1 \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls)) \<in> G\<^sub>c" and
       a4:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Seq C1 C2, (\<sigma>g,\<sigma>l)) \<rightarrow> (c\<^sub>c', (\<sigma>g',\<sigma>l'))" and
       a5:"C1 = Basic fc \<tau> \<or> C1 = Spec rc \<tau>" and 
      a6:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and 
       a8:"(\<Gamma>\<^sub>c,C2,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S,R\<^sub>s,G\<^sub>s)" 
  shows "(\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
          \<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', (\<Sigma>g',\<Sigma>l')) \<and>
          (((\<sigma>g',\<sigma>l'),\<sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<alpha> \<and>
          ((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g',\<sigma>l'),\<sigma>ls)), (((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          (c\<^sub>c' = Seq C1 C2 \<and> c\<^sub>s' = S \<and>  (((\<sigma>g',\<sigma>l'),\<sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi> \<or>
           (\<Gamma>\<^sub>c,(c\<^sub>c', ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)))"
proof-
  have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (S, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (S, (\<Sigma>g,\<Sigma>l))" by auto
  moreover have "(((\<Sigma>g,\<Sigma>l),\<Sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> G\<^sub>s\<^sup>*"  by auto
  moreover have "c\<^sub>c' = Seq Skip C2 \<and> (((\<sigma>g',\<sigma>l'),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls))\<in>\<xi>\<^sub>1 \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)) \<in> G\<^sub>c" 
                 using a5
  proof
    assume a00:"C1 = LanguageCon.com.Basic fc \<tau> "    
    then have "c\<^sub>c' = Seq Skip C2" using stepc_elim_cases1(7)[OF a4] stepc_elim_cases1(5)
      by (metis LanguageCon.com.distinct(1) LanguageCon.com.distinct(37) 
              LanguageCon.com.distinct(43) LanguageCon.com.distinct(45) fst_conv) 
    moreover have "(((\<sigma>g',\<sigma>l'),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls))\<in>\<xi>\<^sub>1 \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)) \<in> G\<^sub>c"  
    proof -
      have " (\<sigma>g',\<sigma>l') = fc (\<sigma>g,\<sigma>l)" using a4[simplified calculation a00]
        by (meson CRef.stepc_elim_cases(6) Pair_inject stepc_elim_cases1(5) 
               stepce_stepc xstate.inject(1))
      then show ?thesis using a3[simplified a00] a2 by auto
    qed
    ultimately show ?thesis by auto    
  next
    assume a00:"C1 = LanguageCon.com.Spec rc \<tau>"
    have c\<^sub>c':"c\<^sub>c' = Seq Skip C2" using stepc_elim_cases1(7)[OF a4[simplified a00]]
    proof -
      obtain cc xx where
        f1: "(c\<^sub>c', (\<sigma>g',\<sigma>l')) = (LanguageCon.com.Seq cc C2, xx) \<and> 
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Spec rc \<tau>, (\<sigma>g,\<sigma>l)) \<rightarrow> (cc, xx)"
        using stepc_elim_cases1(7)[OF a4[simplified a00]]  by force
      moreover have "(cc,(\<sigma>g',\<sigma>l'))\<in> com_step  C1 (\<sigma>g,\<sigma>l)  \<Gamma>\<^sub>c" 
        using a00 calculation Spec_r_com_step by fast
      ultimately show ?thesis
        using  a3 a2 by fast
    qed
    moreover have "(((\<sigma>g',\<sigma>l'),\<sigma>ls), (\<Sigma>g,\<Sigma>l),\<Sigma>ls)\<in>\<xi>\<^sub>1 \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)) \<in> G\<^sub>c"  
    proof-
      have "((\<sigma>g,\<sigma>l), (\<sigma>g',\<sigma>l'))\<in>rc" using a4[simplified calculation a00]
        by (meson CRef.stepc_elim_cases(2) CRef.stepc_elim_cases(6)) 
      then show ?thesis  using a3[simplified a00] a2
        by (metis Spec_r_com_step a00 a4 calculation evstepc_elim_seq(1)) 
    qed
    ultimately show ?thesis  by auto          
  qed 
  moreover have "(\<Gamma>\<^sub>c,(c\<^sub>c', ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(S,((\<Sigma>g,\<Sigma>l),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
    using Impl_Seq_Skip_sim[OF a0' a1 a6    a8] calculation 
    unfolding RGSim_pre_def by auto
  ultimately show ?thesis using a0' a0 a2 unfolding related_transitions_def by fast
qed

lemma spec_tran_basic_sim_cond:assumes 
  a0:"(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and
  a1:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls \<Sigma>g' \<Sigma>l' C.
       (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi> \<and> (C,(\<Sigma>g',\<Sigma>l')) \<in> com_step S1 (\<Sigma>g,\<Sigma>l) \<Gamma>\<^sub>s \<longrightarrow>
       (C = Skip \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s)" and
  a2:    "S1 = LanguageCon.com.Basic fc \<tau> "
obtains \<Sigma>g' \<Sigma>l' where "(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and> 
       (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Skip,(\<Sigma>g',\<Sigma>l'))"
proof-
  have com_step:"(Skip, (fc (\<Sigma>g,\<Sigma>l))) \<in> com_step S1 (\<Sigma>g,\<Sigma>l) \<Gamma>\<^sub>s" using a2 by auto
  moreover obtain \<Sigma>g' \<Sigma>l' where fc:"fc (\<Sigma>g,\<Sigma>l) = (\<Sigma>g',\<Sigma>l')" by fastforce
  ultimately have "((((\<sigma>g,\<sigma>l),\<sigma>ls), (fc (\<Sigma>g,\<Sigma>l), \<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and> 
                         (((\<Sigma>g,\<Sigma>l), \<Sigma>ls), (fc (\<Sigma>g,\<Sigma>l), \<Sigma>ls)) \<in> G\<^sub>s)"
    using a1 a0 by auto
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1,  (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Skip, (\<Sigma>g', \<Sigma>l'))"
    using com_step_Basic com_step a2 fc by fastforce
  ultimately show ?thesis using that fc by auto
qed

lemma spec_tran_spec_sim_cond:assumes 
  a0:"(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and
  a1:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls \<Sigma>g' \<Sigma>l' C.
       (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi> \<and> (C,(\<Sigma>g',\<Sigma>l')) \<in> com_step S1 (\<Sigma>g,\<Sigma>l) \<Gamma>\<^sub>s \<longrightarrow>
       (C = Skip \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s)" and
  a2:    "S1 = Spec r \<tau> "
obtains \<Sigma>g' \<Sigma>l' where "(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and> 
                        (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Skip,(\<Sigma>g',\<Sigma>l'))"
proof-
  {assume a00: "\<exists>\<Sigma>g' \<Sigma>l'. ((\<Sigma>g,\<Sigma>l),(\<Sigma>g',\<Sigma>l')) \<in> r"
    then obtain \<Sigma>g' \<Sigma>l' where a00:" ((\<Sigma>g,\<Sigma>l),(\<Sigma>g',\<Sigma>l')) \<in> r" by auto
    then have "(Skip, (\<Sigma>g',\<Sigma>l')) \<in> com_step S1 (\<Sigma>g,\<Sigma>l) \<Gamma>\<^sub>s" using a2 by auto
    then have "((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and>  (((\<Sigma>g,\<Sigma>l), \<Sigma>ls),  ((\<Sigma>g',\<Sigma>l'), \<Sigma>ls)) \<in> G\<^sub>s)"
      using a1 a0 by auto
    moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Skip, (\<Sigma>g',\<Sigma>l'))"
      using Specc a2 a00 by auto
    ultimately have ?thesis using that by auto  
  }
  moreover
  {assume a00: "\<not>(\<exists>\<Sigma>g' \<Sigma>l'. ((\<Sigma>g,\<Sigma>l),(\<Sigma>g',\<Sigma>l')) \<in> r)"    
    then have "(Stuck, (\<Sigma>g,\<Sigma>l)) \<in> com_step S1 (\<Sigma>g,\<Sigma>l) \<Gamma>\<^sub>s" using a2 by auto    
    then have ?thesis using that a1  a0 by fastforce  
  }
  ultimately show ?thesis  by auto
qed

lemma spec_mod_non_await1:
  assumes 
  a0:"(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and a0':"\<xi>\<subseteq>\<alpha>" and a1:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and a1':"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
  a2:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and  
  a6:"S1 = Basic fc \<tau> \<or> S1 = Spec rc \<tau>" and 
  a7:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls \<Sigma>g' \<Sigma>l' C.
       (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi> \<and> (C,(\<Sigma>g',\<Sigma>l')) \<in> com_step S1 (\<Sigma>g,\<Sigma>l) \<Gamma>\<^sub>s \<longrightarrow>
       (C = Skip \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s)" and
  a8:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" and   
  a11:"C = Stuck" shows
      "\<exists>\<Sigma>g' \<Sigma>l'. ((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g,\<sigma>l),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>              
                  (((\<sigma>g,\<sigma>l),\<sigma>ls),  ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq S1 S2, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, (\<Sigma>g',\<Sigma>l'))"
proof-

  obtain \<Sigma>g' \<Sigma>l' where 
    sim_cond:"(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in>G\<^sub>s \<and> 
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Skip, (\<Sigma>g',\<Sigma>l'))" 
    using a6 spec_tran_basic_sim_cond[OF a0 a7] spec_tran_spec_sim_cond[OF a0 a7] by blast
  moreover have step:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq S1 S2, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Seq Skip S2, (\<Sigma>g',\<Sigma>l'))"
    using Seqc calculation by fastforce
  moreover have x:"(\<Gamma>\<^sub>c,(C,((\<sigma>g,\<sigma>l),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S2, ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
    using  calculation Spec_Seq_Skip_sim[OF a1 a1' a2  a8] 
    unfolding RGSim_pre_def by auto  
  obtain \<Sigma>g'' \<Sigma>l'' where sim:"((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g,\<sigma>l),\<sigma>ls)), (((\<Sigma>g',\<Sigma>l'),\<Sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls))) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>                
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Skip S2, (\<Sigma>g',\<Sigma>l')) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, (\<Sigma>g'',\<Sigma>l'')) \<and>
                  (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls)) \<in>  \<alpha>"   
    using sim_elim_cases_c(4)[OF x[simplified a11],simplified toSeq_def]  by force   
  moreover have "((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g,\<sigma>l),\<sigma>ls)), (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls))) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
    using related_transition_tran[OF subsetD[OF a0' a0]] calculation sim_cond by auto
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq S1 S2, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Stuck, (\<Sigma>g'',\<Sigma>l''))"
    using step calculation by auto
  ultimately show ?thesis by auto    
qed

lemma spec_mod_non_await2:
  assumes 
  a0:"(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and a0':"\<xi>\<subseteq>\<alpha>" and a1:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and a1':"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
  a2:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and  
  a6:"S1 = Basic fc \<tau> \<or> S1 = Spec rc \<tau>" and 
  a7:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls \<Sigma>g' \<Sigma>l' C.
       (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi> \<and> (C,(\<Sigma>g',\<Sigma>l')) \<in> com_step S1 (\<Sigma>g,\<Sigma>l) \<Gamma>\<^sub>s \<longrightarrow>
       (C = Skip \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s)" and
  a8:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" and   
  a11:"C = Fault f" shows
      "\<exists>\<Sigma>g' \<Sigma>l'. ((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g,\<sigma>l),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>              
                  (((\<sigma>g,\<sigma>l),\<sigma>ls),  ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq S1 S2, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, (\<Sigma>g',\<Sigma>l'))"
proof-

  obtain \<Sigma>g' \<Sigma>l' where 
    sim_cond:"(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in>G\<^sub>s \<and> 
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Skip, (\<Sigma>g',\<Sigma>l'))" 
    using a6 spec_tran_basic_sim_cond[OF a0 a7] spec_tran_spec_sim_cond[OF a0 a7] by blast
  moreover have step:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq S1 S2, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Seq Skip S2, (\<Sigma>g',\<Sigma>l'))"
    using Seqc calculation by fastforce
  moreover have x:"(\<Gamma>\<^sub>c,(C,((\<sigma>g,\<sigma>l),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S2, ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
    using  calculation Spec_Seq_Skip_sim[OF a1 a1' a2  a8] 
    unfolding RGSim_pre_def by auto  
  obtain \<Sigma>g'' \<Sigma>l'' where sim:"((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g,\<sigma>l),\<sigma>ls)), (((\<Sigma>g',\<Sigma>l'),\<Sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls))) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>                
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Skip S2, (\<Sigma>g',\<Sigma>l')) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, (\<Sigma>g'',\<Sigma>l'')) \<and>
                  (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls)) \<in>  \<alpha>"   
    using sim_elim_cases_c(3)[OF x[simplified a11],simplified toSeq_def]  by force   
  moreover have "((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g,\<sigma>l),\<sigma>ls)), (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls))) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
    using related_transition_tran[OF subsetD[OF a0' a0]] calculation sim_cond by auto
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq S1 S2, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (Fault f, (\<Sigma>g'',\<Sigma>l''))"
    using step calculation by auto
  ultimately show ?thesis by auto    
qed

lemma spec_mod_non_await3:
  assumes 
  a0:"(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and a0':"\<xi>\<subseteq>\<alpha>" and a1:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and a1':"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
  a2:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and  
  a6:"S1 = Basic fc \<tau> \<or> S1 = Spec rc \<tau>" and 
  a7:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls \<Sigma>g' \<Sigma>l' C.
       (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi> \<and> (C,(\<Sigma>g',\<Sigma>l')) \<in> com_step S1 (\<Sigma>g,\<Sigma>l) \<Gamma>\<^sub>s \<longrightarrow>
       (C = Skip \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s)" and
  a8:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" and   
  a11:"C = LanguageCon.com.Throw" shows
      "\<exists>\<Sigma>g' \<Sigma>l'. ((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g,\<sigma>l),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
              (((\<sigma>g,\<sigma>l),\<sigma>ls),  ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<gamma>\<^sub>a \<and>
              \<gamma>\<^sub>a \<subseteq> \<alpha> \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq S1 S2, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Throw, (\<Sigma>g',\<Sigma>l'))"
proof-

  obtain \<Sigma>g' \<Sigma>l' where 
    sim_cond:"(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in>G\<^sub>s \<and> 
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Skip, (\<Sigma>g',\<Sigma>l'))" 
    using a6 spec_tran_basic_sim_cond[OF a0 a7] spec_tran_spec_sim_cond[OF a0 a7] by blast
  moreover have step:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq S1 S2, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Seq Skip S2, (\<Sigma>g',\<Sigma>l'))"
    using Seqc calculation by fastforce
  moreover have x:"(\<Gamma>\<^sub>c,(C,((\<sigma>g,\<sigma>l),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S2, ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
    using  calculation Spec_Seq_Skip_sim[OF a1 a1' a2  a8] 
    unfolding RGSim_pre_def by auto  
  obtain \<Sigma>g'' \<Sigma>l'' where sim:"((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g,\<sigma>l),\<sigma>ls)), (((\<Sigma>g',\<Sigma>l'),\<Sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls))) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                 (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls)) \<in> \<gamma>\<^sub>a \<and> \<gamma>\<^sub>a \<subseteq> \<alpha> \<and>
                 \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Skip S2, (\<Sigma>g',\<Sigma>l')) \<rightarrow>\<^sub>\<tau>\<^sup>* (Throw, (\<Sigma>g'',\<Sigma>l''))"   
    using sim_elim_cases_c(2)[OF x[simplified a11],simplified toSeq_def]  by force   
  moreover have "((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g,\<sigma>l),\<sigma>ls)), (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls))) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
    using related_transition_tran[OF subsetD[OF a0' a0]] calculation sim_cond by auto
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq S1 S2, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Throw, (\<Sigma>g'',\<Sigma>l''))"
    using step calculation by auto
  ultimately show ?thesis by auto    
qed



lemma spec_mod_non_await4:
  assumes 
  a0:"(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and a0':"\<xi>\<subseteq>\<alpha>" and a1:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and a1':"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
  a2:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and   
  a6:"S1 = Basic fc \<tau> \<or> S1 = Spec rc \<tau>" and 
  a7:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls \<Sigma>g' \<Sigma>l' C.
       (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi> \<and> (C,(\<Sigma>g',\<Sigma>l')) \<in> com_step S1 (\<Sigma>g,\<Sigma>l) \<Gamma>\<^sub>s \<longrightarrow>
       (C = Skip \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s)" and
  a8:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" and 
  a11:"C = Skip" shows
      "\<exists>\<Sigma>g' \<Sigma>l'. ((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g,\<sigma>l),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
            (((\<sigma>g,\<sigma>l),\<sigma>ls),  ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))  \<in> \<gamma>\<^sub>n \<and> \<gamma>\<^sub>n \<subseteq> \<alpha> \<and> 
            \<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq S1 S2,  (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip,(\<Sigma>g',\<Sigma>l'))"
proof-

obtain \<Sigma>g' \<Sigma>l' where 
    sim_cond:"(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in>G\<^sub>s \<and> 
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Skip, (\<Sigma>g',\<Sigma>l'))" 
    using a6 spec_tran_basic_sim_cond[OF a0 a7] spec_tran_spec_sim_cond[OF a0 a7] by blast
  moreover have step:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq S1 S2, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Seq Skip S2, (\<Sigma>g',\<Sigma>l'))"
    using Seqc calculation by fastforce
  moreover have x:"(\<Gamma>\<^sub>c,(C,((\<sigma>g,\<sigma>l),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S2, ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
    using  calculation Spec_Seq_Skip_sim[OF a1 a1' a2   a8] 
    unfolding RGSim_pre_def by auto  
  obtain \<Sigma>g'' \<Sigma>l'' where sim:"((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g,\<sigma>l),\<sigma>ls)), (((\<Sigma>g',\<Sigma>l'),\<Sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls))) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
            (((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls)) \<in> \<gamma>\<^sub>n \<and> \<gamma>\<^sub>n \<subseteq> \<alpha> \<and> 
            \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Skip S2,  (\<Sigma>g',\<Sigma>l')) \<rightarrow>\<^sub>\<tau>\<^sup>* (Skip, (\<Sigma>g'',\<Sigma>l''))"   
    using sim_elim_cases_c(1)[OF x[simplified a11],simplified toSeq_def] by force   
  moreover have "((((\<sigma>g,\<sigma>l),\<sigma>ls),((\<sigma>g,\<sigma>l),\<sigma>ls)), (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls))) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
    using related_transition_tran[OF subsetD[OF a0' a0]] calculation sim_cond by auto
  moreover have "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (LanguageCon.com.Seq S1 S2, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (LanguageCon.com.Skip, (\<Sigma>g'',\<Sigma>l''))"
    using step calculation by auto
  ultimately show ?thesis by auto    
qed

lemma spec_mod_non_await5: assumes 
  a0:"(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and a0':"\<xi>\<subseteq>\<alpha>" and a1:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and a1':"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
  a2:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and  
  a6:"S1 = Basic fc \<tau> \<or> S1 = Spec rc \<tau>" and 
  a7:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls \<Sigma>g' \<Sigma>l' C.
       (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi> \<and> (C,(\<Sigma>g',\<Sigma>l')) \<in> com_step S1 (\<Sigma>g,\<Sigma>l) \<Gamma>\<^sub>s \<longrightarrow>
       (C = Skip \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s)" and
  a8:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" and 
  a9:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (C, (\<sigma>g,\<sigma>l)) \<rightarrow> (c\<^sub>c', (\<sigma>g',\<sigma>l'))"
  shows  "\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
          (\<exists>a b c. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq S1 S2, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, (b,c)) \<and>
                 (\<exists>aa ba ca. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, (b,c)) \<rightarrow> (aa, (ba,ca)) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, (ba,ca)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', (\<Sigma>g',\<Sigma>l')))) \<and>
          (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<alpha> \<and>
           ((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
          (c\<^sub>c' = C \<and> c\<^sub>s' = Seq S1 S2 \<and> (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi> \<or> 
          (\<Gamma>\<^sub>c,(c\<^sub>c',((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s))"
proof-
 obtain \<Sigma>g' \<Sigma>l' where 
   sim_cond:"(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and> ( ((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in>G\<^sub>s \<and> 
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Skip, (\<Sigma>g',\<Sigma>l'))" 
    using a6 spec_tran_basic_sim_cond[OF a0 a7] spec_tran_spec_sim_cond[OF a0 a7] by blast
  moreover have step:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq S1 S2, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Seq Skip S2, (\<Sigma>g',\<Sigma>l'))"
    using Seqc calculation by fastforce
  moreover have x:"(\<Gamma>\<^sub>c,(C,((\<sigma>g,\<sigma>l),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S2, ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
    using  calculation Spec_Seq_Skip_sim[OF a1 a1' a2  a8] 
    unfolding RGSim_pre_def by auto  
  moreover obtain c\<^sub>s' \<Sigma>g'' \<Sigma>l'' where 
        sim:"(\<exists>a b c. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Skip S2,  (\<Sigma>g',\<Sigma>l')) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, (b,c)) \<and>
                   (\<exists>aa ba ca. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, (b,c)) \<rightarrow> (aa, (ba,ca)) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, (ba,ca)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', (\<Sigma>g'',\<Sigma>l'')))) \<and>
            (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls)) \<in> \<alpha> \<and>
             ((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and> 
            (\<Gamma>\<^sub>c,(c\<^sub>c', ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)" 
    apply (rule  sim_elim_cases[OF x,simplified toSeq_def]) using a9 by fastforce
  moreover have G:"((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
    using related_transition_tran[OF subsetD[OF a0' a0]] calculation sim_cond 
    by auto  
  ultimately show ?thesis
  proof -
    obtain cc and cca  and dd  and ccb  and ccc  and dda where
      "(\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Skip S2, \<Sigma>g', \<Sigma>l') \<rightarrow>\<^sub>\<tau>\<^sup>* (cc, cca, dd) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>Some v (cc, cca, dd) \<rightarrow> (ccb, ccc, dda) \<and> 
         \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ccb, ccc, dda) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', \<Sigma>g'', \<Sigma>l'')) \<and> (((\<sigma>g', \<sigma>l'), \<sigma>ls), (\<Sigma>g'', \<Sigma>l''), \<Sigma>ls) \<in> \<alpha> \<and> 
       ((((\<sigma>g, \<sigma>l), \<sigma>ls), (\<sigma>g', \<sigma>l'), \<sigma>ls), ((\<Sigma>g', \<Sigma>l'), \<Sigma>ls), (\<Sigma>g'', \<Sigma>l''), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and> 
     (\<Gamma>\<^sub>c,(c\<^sub>c', (\<sigma>g', \<sigma>l'), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (\<Sigma>g'', \<Sigma>l''), \<Sigma>ls),R\<^sub>s,G\<^sub>s)"
      using sim by blast
    then show ?thesis
      by (meson G converse_rtranclp_into_rtranclp local.step)
  qed
qed

lemma spec_mod_non_await6: assumes 
 a0:"(((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi>" and a0':"\<xi>\<subseteq>\<alpha>" and a1:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and a1':"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
  a2:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and  
  a6:"S1 = Basic fc \<tau> \<or> S1 = Spec rc \<tau>" and 
  a7:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls \<Sigma>g' \<Sigma>l' C.
       (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi> \<and> (C,(\<Sigma>g',\<Sigma>l')) \<in> com_step S1 (\<Sigma>g,\<Sigma>l) \<Gamma>\<^sub>s \<longrightarrow>
       (C = Skip \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s)" and
  a8:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)" and 
  a11:" \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (C, (\<sigma>g,\<sigma>l)) \<rightarrow> (c\<^sub>c', (\<sigma>g',\<sigma>l'))"
  shows  "\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq S1 S2, (\<Sigma>g,\<Sigma>l)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',(\<Sigma>g',\<Sigma>l')) \<and>
                  (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<alpha> \<and> 
                    ((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
                   (c\<^sub>c' = C \<and> c\<^sub>s' = Seq S1 S2 \<and> (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi> \<or> 
          (\<Gamma>\<^sub>c,(c\<^sub>c',((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s',((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s))"
proof- 
   obtain \<Sigma>g' \<Sigma>l' where 
   sim_cond:"(((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and> ( ((\<Sigma>g,\<Sigma>l),\<Sigma>ls),  ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls))\<in>G\<^sub>s \<and> 
              \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (S1, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Skip, (\<Sigma>g',\<Sigma>l'))"  
    using a6 spec_tran_basic_sim_cond[OF a0 a7] spec_tran_spec_sim_cond[OF a0 a7] by blast
  moreover have step:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>\<tau> (Seq S1 S2, (\<Sigma>g,\<Sigma>l)) \<rightarrow> (Seq Skip S2, (\<Sigma>g',\<Sigma>l'))"
    using Seqc calculation by fastforce
  moreover have x:"(\<Gamma>\<^sub>c,(C,((\<sigma>g,\<sigma>l),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq Skip S2, ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
    using  calculation Spec_Seq_Skip_sim[OF a1 a1' a2  a8] 
    unfolding RGSim_pre_def by auto   
  moreover obtain c\<^sub>s' \<Sigma>g'' \<Sigma>l'' where 
        "\<Gamma>\<^sub>s\<turnstile>\<^sub>c (Seq Skip S2, (\<Sigma>g',\<Sigma>l')) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', (\<Sigma>g'',\<Sigma>l'')) \<and>
             (((\<sigma>g',\<sigma>l'),\<sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls)) \<in> \<alpha> \<and>
             ((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and> 
            (\<Gamma>\<^sub>c,(c\<^sub>c', ((\<sigma>g',\<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)" 
    apply (rule  sim_elim_cases[OF x,simplified toSeq_def]) using a11 by fastforce    
  moreover have "((((\<sigma>g,\<sigma>l),\<sigma>ls), ((\<sigma>g',\<sigma>l'),\<sigma>ls)), ((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g'',\<Sigma>l''),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>)"
    using related_transition_tran[OF subsetD[OF a0' a0]] calculation sim_cond 
    by auto
  ultimately show ?thesis 
    by (metis (no_types, lifting) converse_rtranclp_into_rtranclp)
qed


lemma seq_non_await_spec_sim: 
  assumes
 a1:"\<xi> \<subseteq> \<alpha>" and a2:"\<xi>\<^sub>1 \<subseteq> \<alpha>" and
 a3:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and a4:"Sta\<^sub>s \<xi>\<^sub>1 ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and
 a5:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and   
 a9:"S1 = Basic fc \<tau> \<or> S1 = Spec rc \<tau>" and   
 a10:"\<forall>\<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls \<Sigma>g' \<Sigma>l' C.
       (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g,\<Sigma>l),\<Sigma>ls)) \<in> \<xi> \<and> (C,(\<Sigma>g',\<Sigma>l')) \<in> com_step S1 (\<Sigma>g,\<Sigma>l) \<Gamma>\<^sub>s \<longrightarrow>
       (C = Skip \<and> (((\<sigma>g,\<sigma>l),\<sigma>ls),((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> \<xi>\<^sub>1 \<and> (((\<Sigma>g,\<Sigma>l),\<Sigma>ls), ((\<Sigma>g',\<Sigma>l'),\<Sigma>ls)) \<in> G\<^sub>s)" and
 a11:"(\<Gamma>\<^sub>c,C,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,S2,R\<^sub>s,G\<^sub>s)"
shows "(\<Gamma>\<^sub>c,C ,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,Seq S1 S2,R\<^sub>s,G\<^sub>s)"  
  
proof-
  { fix  \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls
    assume "(((\<sigma>g, \<sigma>l), \<sigma>ls), (\<Sigma>g, \<Sigma>l), \<Sigma>ls) \<in> \<xi>"    
    then have "(\<Gamma>\<^sub>c,(C, ((\<sigma>g, \<sigma>l), \<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(Seq S1 S2, ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
       apply (coinduction arbitrary: \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls)
      apply clarsimp
      apply (rule conjId)+ 
             apply (auto simp add: toSeq_def)[1]
             apply (frule spec_mod_non_await1[OF  _ a1 a2 a4 a5  a9 a10 a11],fast+)
             apply (auto simp add: toSeq_def)[1]
            apply (frule spec_mod_non_await2[OF  _ a1 a2 a4 a5  a9 a10 a11],fast+)
             apply (auto simp add: toSeq_def)[1]
           apply (frule spec_mod_non_await3[OF  _ a1 a2 a4 a5  a9 a10 a11],fast+)
             apply (auto simp add: toSeq_def)[1]
            apply (frule spec_mod_non_await4[OF  _ a1 a2 a4 a5  a9 a10 a11],fast+)
         apply (meson a3 sim_env)
        apply (auto simp add: toSeq_def)[1]
        apply (frule spec_mod_non_await5[OF  _ a1 a2 a4 a5  a9 a10 a11],fast+)
       apply (auto simp add: toSeq_def)[1]
       apply (frule spec_mod_non_await6[OF  _ a1 a2 a4 a5  a9 a10 a11],fast+)
      using  a1 by auto   
  } then show ?thesis unfolding RGSim_pre_def by auto
qed

lemma If_branch_sim:
  assumes 
  a1:"\<xi> \<subseteq> \<alpha> \<and> \<gamma>\<^sub>n\<subseteq>\<alpha>" and 
  a2:"Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>)" and 
  a4:"\<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c" and   
  a5:"\<xi>\<^sub>1= \<xi> \<inter> \<up>(b\<^sub>c \<odot> {s. True})" and 
  a6:"\<xi>\<^sub>2= \<xi> \<inter> \<up>(-(b\<^sub>c) \<odot> {s. True} )" and  
  a7:"(((\<sigma>g, \<sigma>l), \<sigma>ls), (\<Sigma>g, \<Sigma>l), \<Sigma>ls) \<in> \<xi>" and
  a9:"(\<Gamma>\<^sub>c,c1\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c\<^sub>s,R\<^sub>s,G\<^sub>s)" and 
  a10:"(\<Gamma>\<^sub>c,c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>2\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,c\<^sub>s,R\<^sub>s,G\<^sub>s)"
shows  
  "(\<Gamma>\<^sub>c,(Cond b\<^sub>c c1\<^sub>c c2\<^sub>c,((\<sigma>g, \<sigma>l), \<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s,((\<Sigma>g, \<Sigma>l), \<Sigma>ls)),R\<^sub>s,G\<^sub>s)"
  using   a7
  proof(coinduction arbitrary: \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls,clarsimp)
  fix \<sigma>g \<sigma>l \<sigma>ls \<Sigma>g \<Sigma>l \<Sigma>ls
    let ?\<sigma>s = "(\<sigma>g::'a,\<sigma>l::'b)" and ?\<Sigma>s = "(\<Sigma>g::'c,\<Sigma>l::'d)"
    let ?\<sigma> = "(?\<sigma>s,\<sigma>ls::'b list)" and ?\<Sigma> = "(?\<Sigma>s,\<Sigma>ls::'d list)"
    assume 
       a0:"(?\<sigma>, ?\<Sigma>) \<in> \<xi>" 
    have a8:"\<xi> \<subseteq> \<alpha>" and a11:"\<gamma>\<^sub>n \<subseteq> \<alpha>"  using a1 by auto           
    have "(?\<sigma>, ?\<Sigma>) \<in> \<alpha>" using a0 a8 by fastforce 
    moreover have "\<forall>\<sigma>' \<Sigma>'. (((?\<sigma>, \<sigma>'), ?\<Sigma>, \<Sigma>') \<in> (R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>)  \<longrightarrow>
                   ((\<sigma>', \<Sigma>') \<in> \<xi> \<or> (\<Gamma>\<^sub>c,(Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, \<sigma>'),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, \<Sigma>'),R\<^sub>s,G\<^sub>s))" 
      using sim_env[OF a0 a2] by blast
    moreover have "\<forall>v c\<^sub>c' \<sigma>g' \<sigma>l'.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, ?\<sigma>s) \<rightarrow> (c\<^sub>c', (\<sigma>g', \<sigma>l')) \<longrightarrow>
           (\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
               (\<exists>a b c. \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, ?\<Sigma>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, (b,c)) \<and>
                      (\<exists>aa ba ca. \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, (b,c)) \<rightarrow> (aa, (ba,ca)) \<and>
                               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (aa, (ba,ca)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s',  (\<Sigma>g', \<Sigma>l')))) \<and>
               (((\<sigma>g', \<sigma>l'),\<sigma>ls), ((\<Sigma>g', \<Sigma>l'),\<Sigma>ls)) \<in> \<alpha> \<and>
               ((?\<sigma>, ((\<sigma>g', \<sigma>l'),\<sigma>ls)), ?\<Sigma>, ((\<Sigma>g', \<Sigma>l'),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (c\<^sub>c' = Cond b\<^sub>c c1\<^sub>c c2\<^sub>c \<and> c\<^sub>s' = c\<^sub>s \<and> (((\<sigma>g', \<sigma>l'),\<sigma>ls), ((\<Sigma>g', \<Sigma>l'),\<Sigma>ls)) \<in> \<xi> \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', ((\<sigma>g', \<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', ((\<Sigma>g', \<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)))"
      by (metis option.distinct(1) stepc_elim_cases1(8)) 
    moreover have "\<forall>c\<^sub>c' \<sigma>g' \<sigma>l'.
           \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, ?\<sigma>s) \<rightarrow> (c\<^sub>c', (\<sigma>g', \<sigma>l')) \<longrightarrow>
           (\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, ?\<Sigma>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', (\<Sigma>g', \<Sigma>l')) \<and>
               (((\<sigma>g', \<sigma>l'),\<sigma>ls), ((\<Sigma>g', \<Sigma>l'),\<Sigma>ls)) \<in> \<alpha> \<and>
               ((?\<sigma>, ((\<sigma>g', \<sigma>l'),\<sigma>ls)), ?\<Sigma>, ((\<Sigma>g', \<Sigma>l'),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (c\<^sub>c' = Cond b\<^sub>c c1\<^sub>c c2\<^sub>c \<and> c\<^sub>s' = c\<^sub>s \<and> (((\<sigma>g', \<sigma>l'),\<sigma>ls), ((\<Sigma>g', \<Sigma>l'),\<Sigma>ls)) \<in> \<xi> \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', ((\<sigma>g', \<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', ((\<Sigma>g', \<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s)))"
    proof -
      {fix c\<^sub>c' \<sigma>g' \<sigma>l'
        assume  a00:"\<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (LanguageCon.com.Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, ?\<sigma>s) \<rightarrow> (c\<^sub>c', (\<sigma>g', \<sigma>l'))"
        then have eqs:"?\<sigma>s = (\<sigma>g', \<sigma>l')"
          using stepc_elim_cases2(1) by fastforce 
        have guar:"((?\<sigma>,?\<sigma>),(?\<Sigma>,?\<Sigma>)) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>"
        using  a4 a7 a0 a8  unfolding related_transitions_def Id_def by blast
       have h:"(c\<^sub>c'=c1\<^sub>c \<and> (\<sigma>g', \<sigma>l')\<in>b\<^sub>c) \<or> (c\<^sub>c'=c2\<^sub>c \<and> (\<sigma>g', \<sigma>l')\<in> -b\<^sub>c)"  
        using stepc_elim_cases2(1)[OF a00] by auto
        {
          assume c:"c\<^sub>c' = c1\<^sub>c \<and> (\<sigma>g', \<sigma>l') \<in> b\<^sub>c"
          then have sig1:"(((\<sigma>g', \<sigma>l'),\<sigma>ls), ?\<Sigma>) \<in> \<xi>\<^sub>1"
            using a0 a5 a6 a7 eqs unfolding eq_rel_def  and_rel_def ext_set_def by auto          
          then have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, ?\<Sigma>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s, ?\<Sigma>s)"          
            by (simp add:  r_into_rtranclp )        
          have x:"(\<Gamma>\<^sub>c,(c1\<^sub>c, ((\<sigma>g', \<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, ?\<Sigma>),R\<^sub>s,G\<^sub>s)" 
            using a9  sig1
            unfolding RGSim_pre_def by auto
          note l = conjI[OF x steps]
        } note l=this        
        {
          assume c:"c\<^sub>c' = c2\<^sub>c \<and> (\<sigma>g', \<sigma>l') \<in> -b\<^sub>c"
          then have sig1:"(((\<sigma>g', \<sigma>l'),\<sigma>ls), ?\<Sigma>) \<in> \<xi>\<^sub>2"
            using a0 a5 a6 a7 eqs unfolding eq_rel_def  and_rel_def ext_set_def by auto
          then have steps:"\<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s,?\<Sigma>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s, ?\<Sigma>s)"          
            by (simp add:  r_into_rtranclp)        
          have x:"(\<Gamma>\<^sub>c,(c2\<^sub>c,((\<sigma>g', \<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s, ?\<Sigma>),R\<^sub>s,G\<^sub>s)" 
            using a10  sig1
            unfolding RGSim_pre_def by auto
          note l = conjI[OF x steps]          
        } 
        then have "\<exists>c\<^sub>s' \<Sigma>g' \<Sigma>l'.
               \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, ?\<Sigma>s) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', (\<Sigma>g', \<Sigma>l')) \<and>
               (((\<sigma>g', \<sigma>l'),\<sigma>ls), ((\<Sigma>g', \<Sigma>l'),\<Sigma>ls)) \<in> \<alpha> \<and>
               ((?\<sigma>, ((\<sigma>g', \<sigma>l'),\<sigma>ls)), ?\<Sigma>, ((\<Sigma>g', \<Sigma>l'),\<Sigma>ls)) \<in> ((G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<and>
               (c\<^sub>c' = Cond b\<^sub>c c1\<^sub>c c2\<^sub>c \<and> c\<^sub>s' = c\<^sub>s \<and> (((\<sigma>g', \<sigma>l'),\<sigma>ls), ((\<Sigma>g', \<Sigma>l'),\<Sigma>ls)) \<in> \<xi> \<or>
                (\<Gamma>\<^sub>c,(c\<^sub>c', ((\<sigma>g', \<sigma>l'),\<sigma>ls)),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', ((\<Sigma>g', \<Sigma>l'),\<Sigma>ls)),R\<^sub>s,G\<^sub>s))" 
          using guar l h  eqs calculation(1) by fastforce
       } thus ?thesis by auto
     qed     
     ultimately show "
        (((\<sigma>g, \<sigma>l), \<sigma>ls), (\<Sigma>g, \<Sigma>l), \<Sigma>ls) \<in> \<alpha> \<and>
        (\<forall>c\<^sub>c' a b.
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>\<tau> (Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c', toSeq ((a, b), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((aa, ba), \<Sigma>ls)) \<and>
                (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                (c\<^sub>c' =Cond b\<^sub>c c1\<^sub>c c2\<^sub>c \<and> c\<^sub>s' = c\<^sub>s \<and> (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))) \<and>
        (\<forall>v c\<^sub>c' a b.
            \<Gamma>\<^sub>c\<turnstile>\<^sub>c\<^sub>(Some v) (Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, toSeq ((\<sigma>g, \<sigma>l), \<sigma>ls)) \<rightarrow> (c\<^sub>c',toSeq ((a, b), \<sigma>ls)) \<longrightarrow>
            (\<exists>c\<^sub>s' aa ba.
                (\<exists>a ab b.
                    \<Gamma>\<^sub>s\<turnstile>\<^sub>c (c\<^sub>s, toSeq ((\<Sigma>g, \<Sigma>l), \<Sigma>ls)) \<rightarrow>\<^sub>\<tau>\<^sup>* (a, ab, b) \<and>
                    (\<exists>ac ad bb.
                        \<Gamma>\<^sub>s\<turnstile>\<^sub>c\<^sub>(Some v) (a, ab, b) \<rightarrow> (ac, ad, bb) \<and> \<Gamma>\<^sub>s\<turnstile>\<^sub>c (ac, ad, bb) \<rightarrow>\<^sub>\<tau>\<^sup>* (c\<^sub>s', toSeq ((aa, ba), \<Sigma>ls)))) \<and>
                (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<alpha> \<and>
                ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), \<sigma>ls), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, ba), \<Sigma>ls) \<in> (G\<^sub>c, G\<^sub>s\<^sup>*)\<^sub>\<alpha> \<and>
                (c\<^sub>c' = Cond b\<^sub>c c1\<^sub>c c2\<^sub>c \<and> c\<^sub>s' = c\<^sub>s \<and> (((a, b), \<sigma>ls), (aa, ba), \<Sigma>ls) \<in> \<xi> \<or>
                 (\<Gamma>\<^sub>c,(c\<^sub>c', (a, b), \<sigma>ls),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,(c\<^sub>s', (aa, ba), \<Sigma>ls),R\<^sub>s,G\<^sub>s)))) \<and>
        (\<forall>a b ba aa bb bc.
            ((((\<sigma>g, \<sigma>l), \<sigma>ls), (a, b), ba), ((\<Sigma>g, \<Sigma>l), \<Sigma>ls), (aa, bb), bc) \<in> ((R\<^sub>c, R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<longrightarrow>
            (((a, b), ba), (aa, bb), bc) \<in> \<xi> \<or> 
            (\<Gamma>\<^sub>c,(Cond b\<^sub>c c1\<^sub>c c2\<^sub>c, (a, b), ba),R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>)  (\<Gamma>\<^sub>s,(c\<^sub>s, (aa, bb), bc),R\<^sub>s,G\<^sub>s))"
       unfolding toSeq_def
      by force
  qed    

lemma If_branch_imp_sound:
  "\<xi> \<subseteq> \<alpha> \<and> \<gamma>\<^sub>n\<subseteq>\<alpha> \<Longrightarrow> Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow> \<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c  \<Longrightarrow>
   \<xi>\<^sub>1= \<xi> \<inter> \<up>(b\<^sub>c \<odot> {s. True}) \<Longrightarrow> \<xi>\<^sub>2= \<xi> \<inter> \<up>(-(b\<^sub>c) \<odot> {s. True} ) \<Longrightarrow>
  (\<Gamma>\<^sub>c,c1\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>1\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow> 
  (\<Gamma>\<^sub>c,c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>2\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow> 
  (\<Gamma>\<^sub>c,Cond b\<^sub>c c1\<^sub>c c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def apply (auto,rule If_branch_sim, auto)
  unfolding RGSim_pre_def by fastforce+ 

lemma If_branch1_imp_sound:
  "\<xi> \<subseteq> \<alpha> \<and> \<gamma>\<^sub>n\<subseteq>\<alpha> \<Longrightarrow> Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow> \<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c  \<Longrightarrow> 
   \<xi> \<subseteq> \<up>(b\<^sub>c \<odot> {s. True}) \<Longrightarrow>
  (\<Gamma>\<^sub>c,c1\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow>  
  (\<Gamma>\<^sub>c,Cond b\<^sub>c c1\<^sub>c c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def apply (auto,rule If_branch_sim, auto)
  unfolding RGSim_pre_def apply auto unfolding ext_set_def by blast

lemma If_branch2_imp_sound:
  "\<xi> \<subseteq> \<alpha> \<and> \<gamma>\<^sub>n\<subseteq>\<alpha> \<Longrightarrow> Sta\<^sub>s \<xi> ((R\<^sub>c,R\<^sub>s\<^sup>*)\<^sub>\<alpha>) \<Longrightarrow> \<forall>\<sigma>. \<sigma>\<in> Domain \<alpha> \<longrightarrow> (\<sigma>, \<sigma>)\<in>G\<^sub>c  \<Longrightarrow> 
   \<xi> \<subseteq> \<up>(-(b\<^sub>c) \<odot> {s. True}) \<Longrightarrow>
  (\<Gamma>\<^sub>c,c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s,G\<^sub>s) \<Longrightarrow>  
  (\<Gamma>\<^sub>c,Cond b\<^sub>c c1\<^sub>c c2\<^sub>c,R\<^sub>c,G\<^sub>c) \<succeq>\<^sub>(\<^sub>\<alpha>\<^sub>;\<^sub>\<xi>\<^sub>\<rhd>\<^sub>\<gamma>\<^sub>n\<^sub>;\<^sub>\<gamma>\<^sub>a\<^sub>) (\<Gamma>\<^sub>s,C\<^sub>s,R\<^sub>s,G\<^sub>s)"
  unfolding RGSim_pre_def apply (auto,rule If_branch_sim, auto)
  unfolding RGSim_pre_def apply auto unfolding ext_set_def by blast


end
    
