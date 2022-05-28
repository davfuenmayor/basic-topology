theory connectedness
  imports separation
begin

(**The sets A and B constitute a separation of a set S.*)
definition Separation ("Separation[_]") 
  where "Separation[\<C>] S A B \<equiv> nonEmpty A \<and> nonEmpty B \<and> Sep[\<C>] A B \<and> S \<^bold>\<approx> A \<^bold>\<or> B"

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
lemma conn_prop3: "MONO \<C> 
        \<Longrightarrow> \<forall>S X. Connected[\<C>] S \<and> S \<^bold>\<preceq> X \<longrightarrow> (\<forall>A B. Separation[\<C>] X A B \<longrightarrow> (S \<^bold>\<preceq> A \<or> S \<^bold>\<preceq> B))"
proof -
  assume mono: "MONO \<C>"
  { fix S X { assume conn: "Connected[\<C>] S" and subset: "S \<^bold>\<preceq> X"
    { fix A B { assume sep: "Separation[\<C>] X A B"
      from subset sep have aux: "S \<^bold>\<approx> (S \<^bold>\<and> A) \<^bold>\<or> (S \<^bold>\<and> B)" by (smt (verit, best) BA_distr1 L10 Separation_def meet_def setequ_char)
      from this mono sep conn have "Disj S A \<or> Disj S B" unfolding Separated_def by (smt (verit, best) Disj_def L3 L5 Sep_sub Separation_def bottom_def setequ_char)
      hence "(S \<^bold>\<preceq> A \<or> S \<^bold>\<preceq> B)" by (smt (verit) Disj_def L14 L5 aux join_def setequ_equ subset_def)
  }}}} thus ?thesis by blast
qed

(**If S is connected and @{text "S \<^bold>\<preceq> X \<^bold>\<preceq> \<C>(S)"} then X is connected too.*)
lemma conn_prop4: "MONO \<C> \<Longrightarrow> \<forall>S X. Connected[\<C>] S \<and> S \<^bold>\<preceq> X \<and> X \<^bold>\<preceq> \<C> S \<longrightarrow> Connected[\<C>] X"
proof -
  assume mono: "MONO \<C>"
  { fix S X { assume conn: "Connected[\<C>] S" and SsubsetX: "S \<^bold>\<preceq> X" and XsubsetCS: "X \<^bold>\<preceq> \<C> S"
    from mono conn SsubsetX have aux: "(\<forall>A B. Separation[\<C>] X A B \<longrightarrow> (S \<^bold>\<preceq> A \<or> S \<^bold>\<preceq> B))" 
      using conn_prop3 by blast
    have "Connected[\<C>] X" proof 
      assume "Separated[\<C>] X"
      from this obtain A and B where sepXAB: "Separation[\<C>] X A B" using Separated_def by blast
      from this aux have "(S \<^bold>\<preceq> A \<or> S \<^bold>\<preceq> B)" by blast
      thus "False" proof
        assume assm: "S \<^bold>\<preceq> A"
        from this mono have "\<C> S \<^bold>\<preceq> \<C> A" by (simp add: MONO_def)
        from this assm sepXAB have 1: "Disj (\<C> S) B" by (metis (mono_tags) Sep_def Sep_sub Separation_def mono subset_def)
        from sepXAB XsubsetCS have 2: "B \<^bold>\<preceq> \<C> S" by (simp add: Separation_def join_def setequ_equ subset_def)
        from sepXAB have 3: "nonEmpty B" by (simp add: Separation_def)
        from 1 2 3 show "False" by (metis Disj_def L10 bottom_def setequ_equ)
      next  
        assume assm: "S \<^bold>\<preceq> B" (*same reasoning as previous case*)
        from this mono have "\<C> S \<^bold>\<preceq> \<C> B" by (simp add: MONO_def)
        from this assm sepXAB have 1: "Disj (\<C> S) A" by (metis (mono_tags) Sep_def Sep_sub Separation_def mono subset_def)
        from sepXAB XsubsetCS have 2: "A \<^bold>\<preceq> \<C> S" by (simp add: Separation_def join_def setequ_equ subset_def)
        from sepXAB have 3: "nonEmpty A" by (simp add: Separation_def)
        from 1 2 3 show "False" by (metis Disj_def L10 bottom_def setequ_equ)
      qed
    qed
  }} thus ?thesis by blast
qed
  
(**If every two points of a set X are contained in some connected subset of X then X is connected.*)
lemma conn_prop5: "MONO \<C> \<Longrightarrow> Cl_2 \<C>
             \<Longrightarrow> \<forall>p q. X p \<and> X q \<longrightarrow> (\<exists>S. S \<^bold>\<preceq> X \<and> Connected[\<C>] S \<and> S p \<and> S q) \<Longrightarrow> Connected[\<C>] X"
proof -
  assume mono: "MONO \<C>" and cl2: "Cl_2 \<C>" 
          and assm: "\<forall>p q. X p \<and> X q \<longrightarrow> (\<exists>S. S \<^bold>\<preceq> X \<and> Connected[\<C>] S \<and> S p \<and> S q)"
  have "Connected[\<C>] X" proof 
    assume sepX: "Separated[\<C>] X"
    from sepX obtain A and B where sepXAB: "Separation[\<C>] X A B" using Separated_def by blast
    hence nonempty: "nonEmpty A \<and> nonEmpty B" by (simp add: Separation_def)
    let ?p="SOME a. A a" and ?q="SOME b. B b" (*well-defined since both A and B are non-empty*)
    from nonempty have "X ?p \<and> X ?q" by (metis Separation_def join_def sepXAB setequ_equ someI_ex)
    from this assm have "\<exists>S. S \<^bold>\<preceq> X \<and> Connected[\<C>] S \<and> S ?p \<and> S ?q" by blast
    from this obtain S where aux: "S \<^bold>\<preceq> X \<and> Connected[\<C>] S \<and> S ?p \<and> S ?q" by blast
    from aux nonempty have 1: "\<not>Disj S A \<and> \<not>Disj S B" by (smt (verit, best) Disj_def bottom_def meet_def  setequ_char someI_ex)
    from aux mono sepXAB have 2: "S \<^bold>\<preceq> A \<or> S \<^bold>\<preceq> B" using conn_prop3 by blast
    from cl2 sepXAB have 3: "Disj A B" by (simp add: Sep_disj Separation_def)
    from 1 2 3 show "False" unfolding Disj_def by (smt (verit, del_insts) bottom_def meet_def setequ_char subset_def)
  qed
  thus ?thesis by simp
qed
  

end