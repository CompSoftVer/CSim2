(*
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory CLanguage
imports "CProof"
begin

definition
  creturn :: "((c_exntype \<Rightarrow> c_exntype) \<Rightarrow> 'c \<times> 'd \<Rightarrow> 'c \<times> 'd)
      \<Rightarrow> (('a \<Rightarrow> 'a) \<Rightarrow> 'c \<times> 'd \<Rightarrow> 'c \<times> 'd)
      \<Rightarrow> ('c \<times> 'd \<Rightarrow> 'a) \<Rightarrow> (('c \<times> 'd),'p,'f,'e) com"
where
  "creturn rtu xfu v \<equiv> (Basic (\<lambda>s. xfu (\<lambda>_. v s) s) None ;; (Basic (rtu (\<lambda>_. Return)) None;; THROW))"

definition
  creturn_void :: "((c_exntype \<Rightarrow> c_exntype) \<Rightarrow> 'c \<times> 'd \<Rightarrow>  'c \<times> 'd) \<Rightarrow> 
                   ( 'c \<times> 'd,'p,'f, 'e) com"
where
  "creturn_void rtu \<equiv> (Basic (rtu (\<lambda>_. Return)) None;; THROW)"

definition
  cbreak :: "((c_exntype \<Rightarrow> c_exntype) \<Rightarrow> 'c \<times> 'd \<Rightarrow>  'c \<times> 'd ) \<Rightarrow> ( 'c \<times> 'd,'p,'f,'e) com"
where
  "cbreak rtu \<equiv> (Basic (rtu (\<lambda>_. Break)) None;; THROW)"

definition
  ccatchbrk :: "('c \<times> 'd \<Rightarrow> c_exntype) \<Rightarrow> ('c \<times> 'd,'p,'f,'e) com"
where
  "ccatchbrk rt \<equiv> Cond {s. rt s = Break} SKIP THROW"

definition
  cchaos :: "('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a,'c,'d,'e) com"
where
  "cchaos upd \<equiv> Spec { (s0,s) . \<exists>v. s = upd v s0 } None"

definition
  "guarded_spec_body F R = Guard F (fst ` R) (Spec R None)"

definition
  seq_creturn :: "((c_exntype \<Rightarrow> c_exntype) \<Rightarrow> 'c \<times> 'd \<Rightarrow> 'c \<times> 'd)
      \<Rightarrow> (('a \<Rightarrow> 'a) \<Rightarrow> 'c \<times> 'd \<Rightarrow> 'c \<times> 'd)
      \<Rightarrow> ('c \<times> 'd \<Rightarrow> 'a) \<Rightarrow> (('c \<times> 'd),'p,'f) Language.com"
where
  "seq_creturn rtu xfu v \<equiv> (Language.Basic (\<lambda>s. xfu (\<lambda>_. v s) s) ;;\<^sub>s (Language.Basic (rtu (\<lambda>_. Return));;\<^sub>s THROW\<^sub>s))"

definition
  seq_creturn_void :: "((c_exntype \<Rightarrow> c_exntype) \<Rightarrow> 'c \<times> 'd \<Rightarrow>  'c \<times> 'd) \<Rightarrow> 
                   ( 'c \<times> 'd,'p,'f) Language.com"
where
  "seq_creturn_void rtu \<equiv> (Language.Basic (rtu (\<lambda>_. Return));;\<^sub>s THROW\<^sub>s)"

definition
  seq_cbreak :: "((c_exntype \<Rightarrow> c_exntype) \<Rightarrow> 'c \<times> 'd \<Rightarrow>  'c \<times> 'd ) \<Rightarrow> ( 'c \<times> 'd,'p,'f) Language.com"
where
  "seq_cbreak rtu \<equiv> (Language.Basic (rtu (\<lambda>_. Break));;\<^sub>s THROW\<^sub>s)"

definition
  seq_ccatchbrk :: "('c \<times> 'd \<Rightarrow> c_exntype) \<Rightarrow> ('c \<times> 'd,'p,'f) Language.com"
where
  "seq_ccatchbrk rt \<equiv> Language.Cond {s. rt s = Break} SKIP\<^sub>s THROW\<^sub>s"

definition
  seq_cchaos :: "('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a,'c,'d) Language.com"
where
  "seq_cchaos upd \<equiv> Language.Spec { (s0,s) . \<exists>v. s = upd v s0 }"

definition
  "seq_guarded_spec_body F R = Language.Guard F (fst ` R) (Language.Spec R)"
end
