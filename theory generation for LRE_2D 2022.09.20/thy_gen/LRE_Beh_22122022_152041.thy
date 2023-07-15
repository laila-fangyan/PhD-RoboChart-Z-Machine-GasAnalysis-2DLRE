theory LRE_Beh_22122022_032042
imports "Z_Machines.Z_Machine"
begin

subsection \<open> Introduction \<close>

text \<open> This theory file is to model the LRE_Beh state machine in Z Machine notations.\<close>

notation undefined ("???")

subsection \<open> type definition \<close>

datatype ('s, 'e) tag =
  State (ofState: 's) | Event (ofEvent: 'e)

abbreviation "is_Event x \<equiv> \<not> is_State x"

type_synonym ('s, 'e) rctrace = "('s, 'e) tag list"

definition wf_rcstore :: "('s, 'e) rctrace \<Rightarrow> 's \<Rightarrow> 's option \<Rightarrow> bool" where
[z_defs]: "wf_rcstore tr st final = (
     length(tr) > 0 
   \<and> tr ! ((length tr) -1) = State st 
   \<and> (final \<noteq> None \<longrightarrow> (\<forall>i<length tr. tr ! i = State (the final) \<longrightarrow> i= (length tr) -1)) 
   \<and> (filter is_State tr) ! (length (filter is_State tr) -1) = State  st)"
   
enumtype St = OCM | MOM | HCM | CAM | initial 
definition [z_defs]: "St = {OCM, MOM, HCM, CAM, initial}" 


enumtype Evt = velocity | position | maneuver | endTask | reqOCM | reqMOM | reqHCM | reqVel | reqHdng | advVel | advHdng 
definition: "Evt = {velocity, position, maneuver, endTask, reqOCM, reqMOM, reqHCM, reqVel, reqHdng, advVel, advHdng}" 


record Coord =
  x :: real
  y :: real
record_default Coord
record Obstacle =
  obsp :: Coord
  id :: nat
record_default Obstacle








consts AvoidanceMargin :: "real"
consts LREHorizon :: "real"
consts LRETemporalHorizon :: "real"
consts ODA_AUV :: "real"
consts ODA_Obs :: "real"
consts StaticObsHorizDist :: "real"
consts StaticObsVertDist :: "real"
consts StaticObsDist :: "real"
consts MinSafeDist :: "real"


text \<open> function definition \<close>

consts TCPA :: " Coord \<times> real \<Rightarrow>real"
consts dist :: " Coord \<Rightarrow> real"
consts inOPEZ :: " Coord \<Rightarrow> bool"
consts CDA :: " Coord \<Rightarrow> real"

subsection \<open> State Space \<close>

zstore LRE_Beh =
  pos :: "Coord"
  hvel :: "real"
  vvel :: "real"
  vel :: "real"
  cstc :: "Obstacle"
  v :: "real"
  h :: "nat"
  hdng :: "nat"
  
  
  
  
  
  
  
  
  
  
  st::"St"
  tr :: "(St, Evt) tag list"
  trg:: "Evt option"
  triggers:: "Evt set"
  where inv: 
    "wf_rcstore tr st (Some final)"

subsection \<open> Operations \<close>

zoperation Trigger= 
params trigger \<in> "triggers"
pre "triggers \<noteq> {}"
update "[
        trg\<Zprime>= Some trigger
        ]"
        
zoperation InitialToOCM =
  over LRE_Beh
  params pos \<in> "Coord" vel \<in> "real" 
  pre "st= initial"
  update "[ st\<Zprime>= OCM
         ,tr\\<Zprime> =tr @ [Event position]@ [Event velocity] @ [State OCM]
         ,trg\\<Zprime> = None
         ,triggers\\<Zprime> = {reqVel, reqHdng, reqMOM}
         ]"
        
zoperation OCMToMOM =
  over LRE_Beh
  pre "st= OCM \<and> vel\<le> \<and> dist(pos)> \<and> \<not>inOPEZ(pos) \<and> trg=Some reqMOM"
  update "[ st\<Zprime>= MOM
         ,tr\\<Zprime> =tr @ [Event reqMOM]@ [Event advVel] @ [State MOM]
         ,trg\\<Zprime> = None
         ,triggers\\<Zprime> = {reqHCM, endTask, reqOCM}
         ]"
        
zoperation MOMToOCM =
  over LRE_Beh
  params pos \<in> "Coord" vel \<in> "real" 
  pre "st= MOM \<and> trg=Some reqOCM"
  update "[ st\<Zprime>= OCM
         ,tr\\<Zprime> =tr @ [Event reqOCM]@ [Event position]@ [Event velocity] @ [State OCM]
         ,trg\\<Zprime> = None
         ,triggers\\<Zprime> = {reqVel, reqHdng, reqMOM}
         ]"
        
zoperation HCMToOCM =
  over LRE_Beh
  params pos \<in> "Coord" vel \<in> "real" 
  pre "st= HCM \<and> trg=Some reqOCM"
  update "[ st\<Zprime>= OCM
         ,tr\\<Zprime> =tr @ [Event reqOCM]@ [Event position]@ [Event velocity] @ [State OCM]
         ,trg\\<Zprime> = None
         ,triggers\\<Zprime> = {reqVel, reqHdng, reqMOM}
         ]"
        
zoperation MOMToHCM =
  over LRE_Beh
  pre "st= MOM \<and> vel\<ge> \<and> dist(pos)\<le>StaticObsDist \<and> CDA(pos)\<ge>MinSafeDist"
  update "[ st\<Zprime>= HCM
         ,tr\\<Zprime> =tr @ [Event advVel] @ [State HCM]
         ,trg\\<Zprime> = None
         ,triggers\\<Zprime> = {reqOCM}
         ]"
        
zoperation MOMToHCM_1 =
  over LRE_Beh
  pre "st= MOM \<and> trg=Some reqHCM"
  update "[ st\<Zprime>= HCM
         ,tr\\<Zprime> =tr @ [Event reqHCM]@ [Event advVel] @ [State HCM]
         ,trg\\<Zprime> = None
         ,triggers\\<Zprime> = {reqOCM}
         ]"
        
zoperation MOMToOCM_1 =
  over LRE_Beh
  params pos \<in> "Coord" vel \<in> "real" 
  pre "st= MOM \<and> inOPEZ(pos)"
  update "[ st\<Zprime>= OCM
         ,tr\\<Zprime> =tr @ [Event position]@ [Event velocity] @ [State OCM]
         ,trg\\<Zprime> = None
         ,triggers\\<Zprime> = {reqVel, reqHdng, reqMOM}
         ]"
        
zoperation HCMToOCM_1 =
  over LRE_Beh
  params pos \<in> "Coord" vel \<in> "real" 
  pre "st= HCM \<and> inOPEZ(pos)"
  update "[ st\<Zprime>= OCM
         ,tr\\<Zprime> =tr @ [Event position]@ [Event velocity] @ [State OCM]
         ,trg\\<Zprime> = None
         ,triggers\\<Zprime> = {reqVel, reqHdng, reqMOM}
         ]"
        
zoperation HCMToMOM =
  over LRE_Beh
  pre "st= HCM \<and> dist(pos)>StaticObsDist"
  update "[ st\<Zprime>= MOM
         ,tr\\<Zprime> =tr @ [Event advVel] @ [State MOM]
         ,trg\\<Zprime> = None
         ,triggers\\<Zprime> = {reqHCM, endTask, reqOCM}
         ]"
        
zoperation OCMToOCM =
  over LRE_Beh
  params v \<in> "real" pos \<in> "Coord" vel \<in> "real" 
  pre "st= OCM \<and> trg=Some reqVel"
  update "[ st\<Zprime>= OCM
         ,tr\\<Zprime> =tr @ [Event reqVel]@ [Event advVel]@ [Event position]@ [Event velocity] @ [State OCM]
         ,trg\\<Zprime> = None
         ,triggers\\<Zprime> = {reqVel, reqHdng, reqMOM}
         ]"
        
zoperation OCMToOCM_1 =
  over LRE_Beh
  params h \<in> "nat" pos \<in> "Coord" vel \<in> "real" 
  pre "st= OCM \<and> trg=Some reqHdng"
  update "[ st\<Zprime>= OCM
         ,tr\\<Zprime> =tr @ [Event reqHdng]@ [Event advHdng]@ [Event position]@ [Event velocity] @ [State OCM]
         ,trg\\<Zprime> = None
         ,triggers\\<Zprime> = {reqVel, reqHdng, reqMOM}
         ]"
        
zoperation MOMToOCM_2 =
  over LRE_Beh
  params pos \<in> "Coord" vel \<in> "real" 
  pre "st= MOM \<and> trg=Some endTask"
  update "[ st\<Zprime>= OCM
         ,tr\\<Zprime> =tr @ [Event endTask]@ [Event advVel]@ [Event position]@ [Event velocity] @ [State OCM]
         ,trg\\<Zprime> = None
         ,triggers\\<Zprime> = {reqVel, reqHdng, reqMOM}
         ]"
        
zoperation HCMToCAM =
  over LRE_Beh
  pre "st= HCM \<and> CDA(pos)<MinSafeDist \<and> CDA(pos)>0"
  update "[ st\<Zprime>= CAM
         ,tr\\<Zprime> =tr @ [Event maneuver] @ [State CAM]
         ,trg\\<Zprime> = None
         ,triggers\\<Zprime> = {reqOCM}
         ]"
        
zoperation MOMToCAM =
  over LRE_Beh
  pre "st= MOM \<and> CDA(pos)<MinSafeDist"
  update "[ st\<Zprime>= CAM
         ,tr\\<Zprime> =tr @ [Event maneuver] @ [State CAM]
         ,trg\\<Zprime> = None
         ,triggers\\<Zprime> = {reqOCM}
         ]"
        
zoperation CAMToOCM =
  over LRE_Beh
  params pos \<in> "Coord" vel \<in> "real" 
  pre "st= CAM \<and> CDA(pos)\<ge>MinSafeDist"
  update "[ st\<Zprime>= OCM
         ,tr\\<Zprime> =tr @ [Event position]@ [Event velocity] @ [State OCM]
         ,trg\\<Zprime> = None
         ,triggers\\<Zprime> = {reqVel, reqHdng, reqMOM}
         ]"
        
zoperation CAMToOCM_1 =
  over LRE_Beh
  params pos \<in> "Coord" vel \<in> "real" 
  pre "st= CAM \<and> trg=Some reqOCM"
  update "[ st\<Zprime>= OCM
         ,tr\\<Zprime> =tr @ [Event reqOCM]@ [Event position]@ [Event velocity] @ [State OCM]
         ,trg\\<Zprime> = None
         ,triggers\\<Zprime> = {reqVel, reqHdng, reqMOM}
         ]"
        

  
definition Init :: "LRE_Beh subst" where
  [z_defs]:
  "Init = 
  [st\<leadsto> ,
   tr\<leadsto> ,
   trg\<leadsto> ,
   triggers\<leadsto> ,
   ]"
(*To be filled in by user*)
  
  
zmachine LRE_BehMachine =
  init Init
  invariant LRE_Beh_inv
  operations  InitialToOCM OCMToMOM MOMToOCM HCMToOCM MOMToHCM MOMToHCM_1 MOMToOCM_1 HCMToOCM_1 HCMToMOM OCMToOCM OCMToOCM_1 MOMToOCM_2 HCMToCAM MOMToCAM CAMToOCM CAMToOCM_1 



subsection \<open> Structural Invariants \<close>

lemma Init_inv [hoare_lemmas]: "Init establishes LRE_Beh_inv"
  by zpog_full

lemma InitialToOCM_inv [hoare_lemmas]: "InitialToOCM (pos, vel) preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma OCMToMOM_inv [hoare_lemmas]: "OCMToMOM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma MOMToOCM_inv [hoare_lemmas]: "MOMToOCM (pos, vel) preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma HCMToOCM_inv [hoare_lemmas]: "HCMToOCM (pos, vel) preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma MOMToHCM_inv [hoare_lemmas]: "MOMToHCM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma MOMToHCM_1_inv [hoare_lemmas]: "MOMToHCM_1() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma MOMToOCM_1_inv [hoare_lemmas]: "MOMToOCM_1 (pos, vel) preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma HCMToOCM_1_inv [hoare_lemmas]: "HCMToOCM_1 (pos, vel) preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma HCMToMOM_inv [hoare_lemmas]: "HCMToMOM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma OCMToOCM_inv [hoare_lemmas]: "OCMToOCM (v, pos, vel) preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma OCMToOCM_1_inv [hoare_lemmas]: "OCMToOCM_1 (h, pos, vel) preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma MOMToOCM_2_inv [hoare_lemmas]: "MOMToOCM_2 (pos, vel) preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma HCMToCAM_inv [hoare_lemmas]: "HCMToCAM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma MOMToCAM_inv [hoare_lemmas]: "MOMToCAM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma CAMToOCM_inv [hoare_lemmas]: "CAMToOCM (pos, vel) preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma CAMToOCM_1_inv [hoare_lemmas]: "CAMToOCM_1 (pos, vel) preserves LRE_Beh_inv"
  by (zpog_full; auto)
  

subsection \<open> Safety Requirements \<close>

zexpr R1 is ""

lemma  "Init establishes R1"
  by zpog_full

lemma "InitialToOCM (pos, vel) preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "OCMToMOM() preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "MOMToOCM (pos, vel) preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "HCMToOCM (pos, vel) preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "MOMToHCM() preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "MOMToHCM_1() preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "MOMToOCM_1 (pos, vel) preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "HCMToOCM_1 (pos, vel) preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "HCMToMOM() preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "OCMToOCM (v, pos, vel) preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "OCMToOCM_1 (h, pos, vel) preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "MOMToOCM_2 (pos, vel) preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "HCMToCAM() preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "MOMToCAM() preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "CAMToOCM (pos, vel) preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma "CAMToOCM_1 (pos, vel) preserves R1 under LRE_Beh_inv"
  by (zpog_full; auto)
  

definition [z_defs]: "LRE_Beh_axioms = ()"

lemma LRE_Beh_deadlock_free: "LRE_Beh_axioms  \<Longrightarrow> deadlock_free LRE_BehMachine" 
  unfolding LRE_BehMachine_def
  by deadlock_free
end

