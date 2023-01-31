theory connectedness
  imports separation
begin

(**The sets A and B constitute a separation of a set S.*)
definition Separation ("Separation[_]") 
  where "Separation[\<C>] S A B \<equiv> nonEmpty A \<and> nonEmpty B \<and> Sep[\<C>] A B \<and> S \<approx> A \<^bold>\<or> B"

(**A set is called separated if it has a separation.*)
definition Separated ("Separated[_]")
  where "Separated[\<C>] S \<equiv> \<exists>A B. Separation[\<C>] S A B"

(**A set is called connected if it has no separation.*)
abbreviation Connected ("Connected[_]")
  where "Connected[\<C>] S \<equiv> \<not>Separated[\<C>] S"

(**Empty sets and singletons are connected.*)
lemma conn_prop1: "Connected[\<C>] \<^bold>\<bottom>" by (smt (verit, best) L10 L6 Separated_def Separation_def bottom_def setequ_equ subset_def)
lemma conn_prop2: "Cl_2 \<C> \<Longrightarrow> \<forall>x. Connected[\<C>] \<lbrace>x\<rbrace>" by (smt (verit, best) singleton_def Disj_def Sep_disj Separated_def Separation_def bottom_def join_def meet_def setequ_equ)

(**A connected subset of a separated set X = (A|B) is contained in either A or B. *)
lemma conn_prop3: assumes mono: "MONO \<C>"
              shows "\<forall>S X. Connected[\<C>] S \<and> S \<preceq> X \<longrightarrow> (\<forall>A B. Separation[\<C>] X A B \<longrightarrow> (S \<preceq> A \<or> S \<preceq> B))"
proof -
  { fix S X { assume conn: "Connected[\<C>] S" and subset: "S \<preceq> X"
    { fix A B { assume sep: "Separation[\<C>] X A B"
      from subset sep have aux: "S \<approx> (S \<^bold>\<and> A) \<^bold>\<or> (S \<^bold>\<and> B)" by (smt (verit, best) BA_distr1 L10 Separation_def meet_def setequ_char)
      from this mono sep conn have "Disj S A \<or> Disj S B" unfolding Separated_def by (smt (verit, best) Disj_char L3 L5 Sep_sub Separation_def bottom_def setequ_char)
        hence "(S \<preceq> A \<or> S \<preceq> B)" by (smt (verit) Disj_def L14 L5 aux join_def setequ_equ subset_def)
  }}}} thus ?thesis by blast
qed

(**If S is connected and @{text "S \<preceq> X \<preceq> \<C>(S)"} then X is connected too.*)
lemma conn_prop4: assumes mono: "MONO \<C>" 
                  shows "\<forall>S X. Connected[\<C>] S \<and> S \<preceq> X \<and> X \<preceq> \<C> S \<longrightarrow> Connected[\<C>] X"
proof -
  { fix S X { assume conn: "Connected[\<C>] S" and SsubsetX: "S \<preceq> X" and XsubsetCS: "X \<preceq> \<C> S"
    from mono conn SsubsetX have aux: "(\<forall>A B. Separation[\<C>] X A B \<longrightarrow> (S \<preceq> A \<or> S \<preceq> B))" 
      using conn_prop3 by blast
    have "Connected[\<C>] X" proof 
      assume "Separated[\<C>] X"
      from this obtain A and B where sepXAB: "Separation[\<C>] X A B" using Separated_def by blast
      from this aux have "(S \<preceq> A \<or> S \<preceq> B)" by blast
      thus "False" proof
        assume assm: "S \<preceq> A"
        from this mono have "\<C> S \<preceq> \<C> A" by (simp add: MONO_def)
        from this assm sepXAB have 1: "Disj (\<C> S) B" by (metis (mono_tags) Sep_def Sep_sub Separation_def mono subset_def)
        from sepXAB XsubsetCS have 2: "B \<preceq> \<C> S" by (simp add: Separation_def join_def setequ_equ subset_def)
        from sepXAB have 3: "nonEmpty B" by (simp add: Separation_def)
        from 1 2 3 show "False" by (metis Disj_char L10 bottom_def setequ_equ)
      next  
        assume assm: "S \<preceq> B" (*same reasoning as previous case*)
        from this mono have "\<C> S \<preceq> \<C> B" by (simp add: MONO_def)
        from this assm sepXAB have 1: "Disj (\<C> S) A" by (metis (mono_tags) Sep_def Sep_sub Separation_def mono subset_def)
        from sepXAB XsubsetCS have 2: "A \<preceq> \<C> S" by (simp add: Separation_def join_def setequ_equ subset_def)
        from sepXAB have 3: "nonEmpty A" by (simp add: Separation_def)
        from 1 2 3 show "False" by (metis Disj_char L10 bottom_def setequ_equ)
      qed
    qed
  }} thus ?thesis by blast
qed
  
(**If every two points of a set X are contained in some connected subset of X then X is connected.*)
lemma conn_prop5: assumes mono: \<open>MONO \<C>\<close> and cl2: \<open>Cl_2 \<C>\<close> shows
 \<open>(\<forall>p q. X p \<and> X q \<and> (\<exists>S. S \<preceq> X \<and> Connected[\<C>] S \<and> S p \<and> S q)) \<longrightarrow> Connected[\<C>] X\<close>
proof -
{ assume premise: \<open>\<forall>p q. X p \<and> X q \<and> (\<exists>S. S \<preceq> X \<and> Connected[\<C>] S \<and> S p \<and> S q)\<close>
  have \<open>Connected[\<C>] X\<close> proof
    assume \<open>Separated[\<C>] X\<close>
    then obtain A and B where sepXAB: \<open>Separation[\<C>] X A B\<close> 
      using Separated_def by blast
    hence nonempty: \<open>nonEmpty A \<and> nonEmpty B\<close> 
      by (simp add: Separation_def)
    let ?p = \<open>SOME a. A a\<close> and ?q = \<open>SOME b. B b\<close> (*since A and B are non-empty*)
    from nonempty have \<open>X ?p \<and> X ?q\<close> 
      by (simp add: premise)
    hence \<open>\<exists>S. S \<preceq> X \<and> Connected[\<C>] S \<and> S ?p \<and> S ?q\<close> 
      by (simp add: premise)
    then obtain S where aux: \<open>S \<preceq> X \<and> Connected[\<C>] S \<and> S ?p \<and> S ?q\<close> ..
    from aux nonempty have \<open>\<not>Disj S A \<and> \<not>Disj S B\<close> 
      by (metis Disj_def someI)
    moreover from aux mono sepXAB have \<open>S \<preceq> A \<or> S \<preceq> B\<close> 
      using conn_prop3 by blast
    moreover from cl2 sepXAB have \<open>Disj A B\<close> 
      by (simp add: Sep_disj Separation_def)
    ultimately show False
      by (metis (mono_tags, lifting) Disj_def subset_def)
  qed
} thus ?thesis ..
qed

end