theory LRE_Beh_24092022_074704
imports "Z_Machines.Z_Machine"
begin

notation undefined ("???")

subsection \<open> Introduction \<close>

text \<open> This theory file is to model the LRE_Beh state machine in Z Machine notations.\<close>

subsection \<open> type definition \<close>

enumtype ProperState = OCM | MOM | HCM | CAM | initial 

definition "ProperState = {OCM, MOM, HCM, CAM, initial}" 

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
consts inOPEZ :: " Coord \<Rightarrow> bool"
consts CDA :: " Coord \<Rightarrow> real"
consts dist :: " Coord \<Rightarrow> real"

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
  
  
  
  
  
  
  
  
  
  
  event_velocity::"bool"
  event_position::"bool"
  event_maneuver::"bool"
  event_endTask::"bool"
  event_reqOCM::"bool"
  event_reqMOM::"bool"
  event_reqHCM::"bool"
  event_reqVel::"bool"
  event_reqHdng::"bool"
  event_advVel::"bool"
  event_advHdng::"bool"
  act_st::"ProperState"
  desired_st::"ProperState set"
  clock::"integer"
where inv: "To be entered manually"

subsection \<open> Operations \<close>

zoperation InitialToOCM =
  over LRE_Beh
  params pos \<in> "Coord" vel \<in> "real" 
  pre "act_st= initial"
  update "[ act_st\<Zprime>= OCM
  		  , desired_st\<Zprime>= {MOM, OCM, OCM}
          , event_position\<Zprime> = True
          , event_velocity\<Zprime> = True
          ]"
        
zoperation OCMToMOM =
  over LRE_Beh
  pre "act_st= OCM \<and> vel\<le> \<and> dist(pos)> \<and> \<not>inOPEZ(pos) \<and> event_reqMOM"
  update "[ act_st\<Zprime>= MOM
  		  , desired_st\<Zprime>= {OCM, HCM, HCM, OCM, OCM, CAM}
          , event_advVel\<Zprime> = True
          ]"
        
zoperation MOMToOCM =
  over LRE_Beh
  params pos \<in> "Coord" vel \<in> "real" 
  pre "act_st= MOM \<and> event_reqOCM"
  update "[ act_st\<Zprime>= OCM
  		  , desired_st\<Zprime>= {MOM, OCM, OCM}
          , event_position\<Zprime> = True
          , event_velocity\<Zprime> = True
          ]"
        
zoperation HCMToOCM =
  over LRE_Beh
  params pos \<in> "Coord" vel \<in> "real" 
  pre "act_st= HCM \<and> event_reqOCM"
  update "[ act_st\<Zprime>= OCM
  		  , desired_st\<Zprime>= {MOM, OCM, OCM}
          , event_position\<Zprime> = True
          , event_velocity\<Zprime> = True
          ]"
        
zoperation MOMToHCM =
  over LRE_Beh
  pre "act_st= MOM \<and> vel\<ge> \<and> dist(pos)\<le>StaticObsDist \<and> CDA(pos)\<ge>MinSafeDist"
  update "[ act_st\<Zprime>= HCM
  		  , desired_st\<Zprime>= {OCM, OCM, MOM, CAM}
          , event_advVel\<Zprime> = True
          ]"
        
zoperation MOMToHCM =
  over LRE_Beh
  pre "act_st= MOM \<and> event_reqHCM"
  update "[ act_st\<Zprime>= HCM
  		  , desired_st\<Zprime>= {OCM, OCM, MOM, CAM}
          , event_advVel\<Zprime> = True
          ]"
        
zoperation MOMToOCM =
  over LRE_Beh
  params pos \<in> "Coord" vel \<in> "real" 
  pre "act_st= MOM \<and> inOPEZ(pos)"
  update "[ act_st\<Zprime>= OCM
  		  , desired_st\<Zprime>= {MOM, OCM, OCM}
          , event_position\<Zprime> = True
          , event_velocity\<Zprime> = True
          ]"
        
zoperation HCMToOCM =
  over LRE_Beh
  params pos \<in> "Coord" vel \<in> "real" 
  pre "act_st= HCM \<and> inOPEZ(pos)"
  update "[ act_st\<Zprime>= OCM
  		  , desired_st\<Zprime>= {MOM, OCM, OCM}
          , event_position\<Zprime> = True
          , event_velocity\<Zprime> = True
          ]"
        
zoperation HCMToMOM =
  over LRE_Beh
  pre "act_st= HCM \<and> dist(pos)>StaticObsDist"
  update "[ act_st\<Zprime>= MOM
  		  , desired_st\<Zprime>= {OCM, HCM, HCM, OCM, OCM, CAM}
          , event_advVel\<Zprime> = True
          ]"
        
zoperation OCMToOCM =
  over LRE_Beh
  params v \<in> "real" pos \<in> "Coord" vel \<in> "real" 
  pre "act_st= OCM \<and> event_reqVel"
  update "[ act_st\<Zprime>= OCM
  		  , desired_st\<Zprime>= {MOM, OCM, OCM}
         , event_advVel\<Zprime> = True
          , event_position\<Zprime> = True
          , event_velocity\<Zprime> = True
          ]"
        
zoperation OCMToOCM =
  over LRE_Beh
  params h \<in> "nat" pos \<in> "Coord" vel \<in> "real" 
  pre "act_st= OCM \<and> event_reqHdng"
  update "[ act_st\<Zprime>= OCM
  		  , desired_st\<Zprime>= {MOM, OCM, OCM}
         , event_advHdng\<Zprime> = True
          , event_position\<Zprime> = True
          , event_velocity\<Zprime> = True
          ]"
        
zoperation MOMToOCM =
  over LRE_Beh
  params pos \<in> "Coord" vel \<in> "real" 
  pre "act_st= MOM \<and> event_endTask"
  update "[ act_st\<Zprime>= OCM
  		  , desired_st\<Zprime>= {MOM, OCM, OCM}
         , event_advVel\<Zprime> = True
          , event_position\<Zprime> = True
          , event_velocity\<Zprime> = True
          ]"
        
zoperation HCMToCAM =
  over LRE_Beh
  pre "act_st= HCM \<and> CDA(pos)<MinSafeDist \<and> CDA(pos)>0"
  update "[ act_st\<Zprime>= CAM
  		  , desired_st\<Zprime>= {OCM, OCM}
          , event_maneuver\<Zprime> = True
          ]"
        
zoperation MOMToCAM =
  over LRE_Beh
  pre "act_st= MOM \<and> CDA(pos)<MinSafeDist"
  update "[ act_st\<Zprime>= CAM
  		  , desired_st\<Zprime>= {OCM, OCM}
          , event_maneuver\<Zprime> = True
          ]"
        
zoperation CAMToOCM =
  over LRE_Beh
  params pos \<in> "Coord" vel \<in> "real" 
  pre "act_st= CAM \<and> CDA(pos)\<ge>MinSafeDist"
  update "[ act_st\<Zprime>= OCM
  		  , desired_st\<Zprime>= {MOM, OCM, OCM}
          , event_position\<Zprime> = True
          , event_velocity\<Zprime> = True
          ]"
        
zoperation CAMToOCM =
  over LRE_Beh
  params pos \<in> "Coord" vel \<in> "real" 
  pre "act_st= CAM \<and> event_reqOCM"
  update "[ act_st\<Zprime>= OCM
  		  , desired_st\<Zprime>= {MOM, OCM, OCM}
          , event_position\<Zprime> = True
          , event_velocity\<Zprime> = True
          ]"
        
zoperation Shine =
  over LRE_Beh
  params s\<in>"{act_st}"
  
definition Init :: "LRE_Beh subst" where
  [z_defs]:
  "Init = 
  [\<leadsto>]"
(*To be filled in by user*)
  
  
zmachine LRE_BehMachine =
  init Init
  operations  InitialToOCM OCMToMOM MOMToOCM HCMToOCM MOMToHCM MOMToHCM MOMToOCM HCMToOCM HCMToMOM OCMToOCM OCMToOCM MOMToOCM HCMToCAM MOMToCAM CAMToOCM CAMToOCM Shine

animate LRE_BehMachine


subsection \<open> Structural Invariants \<close>

lemma Init_inv: "Init establishes LRE_Beh_inv"
  by zpog_full

lemma InitialToOCM_inv: "InitialToOCM (pos, vel) preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma OCMToMOM_inv: "OCMToMOM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma MOMToOCM_inv: "MOMToOCM (pos, vel) preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma HCMToOCM_inv: "HCMToOCM (pos, vel) preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma MOMToHCM_inv: "MOMToHCM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma HCMToMOM_inv: "HCMToMOM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma OCMToOCM_inv: "OCMToOCM (v, pos, vel) preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma OCMToOCM_inv: "OCMToOCM (h, pos, vel) preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma HCMToCAM_inv: "HCMToCAM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma MOMToCAM_inv: "MOMToCAM() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma CAMToOCM_inv: "CAMToOCM (pos, vel) preserves LRE_Beh_inv"
  by (zpog_full; auto)
  

end

