theory Movement_23082022_113730
imports "Z_Machines.Z_Machine"
begin

notation undefined ("???")

subsection \<open> Introduction \<close>

text \<open> This theory file is to model the Movement state machine in Z Machine notations.\<close>

subsection \<open> type definition \<close>

enumtype ProperState = initial | Waiting | Going | Found | final | Avoiding | TryingAgain | AvoidingAgain | GettingOut 

definition "ProperState = {initial, Waiting, Going, Found, final, Avoiding, TryingAgain, AvoidingAgain, GettingOut}" 

enumtype Status = noGas | gasD

definition "Status = {noGas, gasD}"

enumtype Angle = Left | Right | Back | Front

definition "Angle = {Left, Right, Back, Front}"

enumtype Loc = left | right | front

definition "Loc = {left, right, front}"

type_synonym Chem= "nat"
  
type_synonym Intensity= "nat"
  
record GasSensor =
  c :: Chem
  i :: Intensity
record_default GasSensor
consts lv :: "real"
consts evadeTime :: "nat"
consts stuckPeriod :: "nat"
consts stuckDist :: "real"
consts outPeriod :: "nat"





text \<open> function definition \<close>


zfun analysis(gs::" GasSensor list ")::Status
precondition "size(gs)>0"
postcondition "\<exists> x::nat. 0<x\<and>x\<le>size(gs)\<and>i(gs!x)>0 \<longrightarrow> result= (gasD)"
postcondition "\<forall> y::nat. 0<y\<and>y\<le>size(gs)\<and>i(gs!y)= (0) \<longrightarrow> result= (noGas)"

zfun goreq(i1::Intensity, i2::Intensity):: bool
postcondition "result= (i1>i2)"

zfun intensity(gs::" GasSensor list ")::Intensity
precondition "size(gs)>0"
postcondition "\<forall> x::nat. 0<x\<and>x\<le>size(gs) \<longrightarrow> goreq(result, i(gs!x))"
postcondition "\<exists> y::nat. 0<y\<and>y\<le>size(gs) \<longrightarrow> result= (i(gs!y))"

zfun location(gs::" GasSensor list ")::Angle
precondition "size(gs)>0"
postcondition "\<exists> x::nat. 0<x\<and>x\<le>size(gs) \<longrightarrow> i(gs!x)= (intensity(gs))\<and>result= (angle(x))"

zfun angle(x:: nat)::Angle

subsection \<open> State Space \<close>

zstore Movement =
  
  
  
  
  
  a :: "Angle"
  d0 :: "real"
  d1 :: "real"
  l :: "Loc"
  event_resume::"bool"
  event_stop::"bool"
  event_flag::"bool"
  act_st::"ProperState"
  desired_st::"ProperState set"
where inv: "To be entered manually"

subsection \<open> Operations \<close>

zoperation InitialToWaiting =
  over Movement
  pre "act_st= initial"
  update "[ act_st\<Zprime>= Waiting
  		  , desired_st\<Zprime>= {Going, Waiting, Found}
          , randomWalk()
          ]"
        
zoperation WaitingToGoing =
  over Movement
  params a \<in> "Angle" 
  pre "act_st= Waiting"
  update "[ act_st\<Zprime>= Going
  		  , desired_st\<Zprime>= {Going, Found, Avoiding, Waiting}
          , move(lv, a)
          ]"
        
zoperation GoingToGoing =
  over Movement
  params a \<in> "Angle" 
  pre "act_st= Going"
  update "[ act_st\<Zprime>= Going
  		  , desired_st\<Zprime>= {Going, Found, Avoiding, Waiting}
          , move(lv, a)
          ]"
        
zoperation GoingToFound =
  over Movement
  pre "act_st= Going \<and> event_stop"
  update "[ act_st\<Zprime>= Found
  		  , desired_st\<Zprime>= {final}
          , move(0, Front)
          , event_flag\<Zprime> = True
          ]"
        
zoperation FoundToFinal =
  over Movement
  pre "act_st= Found"
  update "[ act_st\<Zprime>= final
  		  , desired_st\<Zprime>= {}
          ]"
        
zoperation GoingToAvoiding =
  over Movement
  params l \<in> "Loc" d0 \<in> "real" 
  pre "act_st= Going"
  update "[ act_st\<Zprime>= Avoiding
  		  , desired_st\<Zprime>= {TryingAgain, Found, Waiting}
          , changeDirection(l)
          , Wait(?)
          ]"
        
zoperation AvoidingToTryingAgain =
  over Movement
  params a \<in> "Angle" 
  pre "act_st= Avoiding"
  update "[ act_st\<Zprime>= TryingAgain
  		  , desired_st\<Zprime>= {TryingAgain, Found, Waiting, AvoidingAgain}
          , move(lv, a)
          ]"
        
zoperation TryingAgainToTryingAgain =
  over Movement
  params a \<in> "Angle" 
  pre "act_st= TryingAgain"
  update "[ act_st\<Zprime>= TryingAgain
  		  , desired_st\<Zprime>= {TryingAgain, Found, Waiting, AvoidingAgain}
          , move(lv, a)
          ]"
        
zoperation TryingAgainToFound =
  over Movement
  pre "act_st= TryingAgain \<and> event_stop"
  update "[ act_st\<Zprime>= Found
  		  , desired_st\<Zprime>= {final}
          , move(0, Front)
          , event_flag\<Zprime> = True
          ]"
        
zoperation TryingAgainToWaiting =
  over Movement
  pre "act_st= TryingAgain \<and> event_resume"
  update "[ act_st\<Zprime>= Waiting
  		  , desired_st\<Zprime>= {Going, Waiting, Found}
          , randomWalk()
          ]"
        
zoperation TryingAgainToAvoidingAgain =
  over Movement
  params l \<in> "Loc" d1 \<in> "real" 
  pre "act_st= TryingAgain"
  update "[ act_st\<Zprime>= AvoidingAgain
  		  , desired_st\<Zprime>= {Avoiding, GettingOut, Found, Waiting}
         
          ]"
        
zoperation AvoidingAgainToAvoiding =
  over Movement
  params d0 \<in> "real" 
  pre "act_st= AvoidingAgain"
  update "[ act_st\<Zprime>= Avoiding
  		  , desired_st\<Zprime>= {TryingAgain, Found, Waiting}
          , changeDirection(l)
          , Wait(?)
          ]"
        
zoperation AvoidingAgainToGettingOut =
  over Movement
  pre "act_st= AvoidingAgain"
  update "[ act_st\<Zprime>= GettingOut
  		  , desired_st\<Zprime>= {Going, Found, Waiting}
          , shortRandomWalk()
          , Wait(?)
          ]"
        
zoperation GettingOutToGoing =
  over Movement
  params a \<in> "Angle" 
  pre "act_st= GettingOut"
  update "[ act_st\<Zprime>= Going
  		  , desired_st\<Zprime>= {Going, Found, Avoiding, Waiting}
          , move(lv, a)
          ]"
        
zoperation WaitingToWaiting =
  over Movement
  pre "act_st= Waiting \<and> event_resume"
  update "[ act_st\<Zprime>= Waiting
  		  , desired_st\<Zprime>= {Going, Waiting, Found}
          , randomWalk()
          ]"
        
zoperation WaitingToFound =
  over Movement
  pre "act_st= Waiting \<and> event_stop"
  update "[ act_st\<Zprime>= Found
  		  , desired_st\<Zprime>= {final}
          , move(0, Front)
          , event_flag\<Zprime> = True
          ]"
        
zoperation GettingOutToFound =
  over Movement
  pre "act_st= GettingOut \<and> event_stop"
  update "[ act_st\<Zprime>= Found
  		  , desired_st\<Zprime>= {final}
          , move(0, Front)
          , event_flag\<Zprime> = True
          ]"
        
zoperation AvoidingAgainToFound =
  over Movement
  pre "act_st= AvoidingAgain \<and> event_stop"
  update "[ act_st\<Zprime>= Found
  		  , desired_st\<Zprime>= {final}
          , move(0, Front)
          , event_flag\<Zprime> = True
          ]"
        
zoperation AvoidingToFound =
  over Movement
  pre "act_st= Avoiding \<and> event_stop"
  update "[ act_st\<Zprime>= Found
  		  , desired_st\<Zprime>= {final}
          , move(0, Front)
          , event_flag\<Zprime> = True
          ]"
        
zoperation AvoidingToWaiting =
  over Movement
  pre "act_st= Avoiding \<and> event_resume"
  update "[ act_st\<Zprime>= Waiting
  		  , desired_st\<Zprime>= {Going, Waiting, Found}
          , randomWalk()
          ]"
        
zoperation GettingOutToWaiting =
  over Movement
  pre "act_st= GettingOut \<and> event_resume"
  update "[ act_st\<Zprime>= Waiting
  		  , desired_st\<Zprime>= {Going, Waiting, Found}
          , randomWalk()
          ]"
        
zoperation AvoidingAgainToWaiting =
  over Movement
  pre "act_st= AvoidingAgain \<and> event_resume"
  update "[ act_st\<Zprime>= Waiting
  		  , desired_st\<Zprime>= {Going, Waiting, Found}
          , randomWalk()
          ]"
        
zoperation GoingToWaiting =
  over Movement
  pre "act_st= Going \<and> event_resume"
  update "[ act_st\<Zprime>= Waiting
  		  , desired_st\<Zprime>= {Going, Waiting, Found}
          , randomWalk()
          ]"
        
zoperation Shine =
  over Movement
  params s\<in>"{act_st}"
  
definition Init :: "Movement subst" where
  [z_defs]:
  "Init = 
  [\<leadsto>]"
(*To be filled in by user*)
  
  
zmachine MovementMachine =
  init Init
  operations  InitialToWaiting WaitingToGoing GoingToGoing GoingToFound FoundToFinal GoingToAvoiding AvoidingToTryingAgain TryingAgainToTryingAgain TryingAgainToFound TryingAgainToWaiting TryingAgainToAvoidingAgain AvoidingAgainToAvoiding AvoidingAgainToGettingOut GettingOutToGoing WaitingToWaiting WaitingToFound GettingOutToFound AvoidingAgainToFound AvoidingToFound AvoidingToWaiting GettingOutToWaiting AvoidingAgainToWaiting GoingToWaiting Shine

animate MovementMachine


subsection \<open> Structural Invariants \<close>

lemma Init_inv: "Init establishes Movement_inv"
  by zpog_full

lemma InitialToWaiting_inv: "InitialToWaiting() preserves Movement_inv"
  by (zpog_full; auto)
  
lemma WaitingToGoing_inv: "WaitingToGoing l preserves Movement_inv"
  by (zpog_full; auto)
  
lemma GoingToGoing_inv: "GoingToGoing l preserves Movement_inv"
  by (zpog_full; auto)
  
lemma GoingToFound_inv: "GoingToFound() preserves Movement_inv"
  by (zpog_full; auto)
  
lemma FoundToFinal_inv: "FoundToFinal() preserves Movement_inv"
  by (zpog_full; auto)
  
lemma GoingToAvoiding_inv: "GoingToAvoiding l preserves Movement_inv"
  by (zpog_full; auto)
  
lemma AvoidingToTryingAgain_inv: "AvoidingToTryingAgain l preserves Movement_inv"
  by (zpog_full; auto)
  
lemma TryingAgainToTryingAgain_inv: "TryingAgainToTryingAgain l preserves Movement_inv"
  by (zpog_full; auto)
  
lemma TryingAgainToFound_inv: "TryingAgainToFound() preserves Movement_inv"
  by (zpog_full; auto)
  
lemma TryingAgainToWaiting_inv: "TryingAgainToWaiting() preserves Movement_inv"
  by (zpog_full; auto)
  
lemma TryingAgainToAvoidingAgain_inv: "TryingAgainToAvoidingAgain l preserves Movement_inv"
  by (zpog_full; auto)
  
lemma AvoidingAgainToAvoiding_inv: "AvoidingAgainToAvoiding l preserves Movement_inv"
  by (zpog_full; auto)
  
lemma AvoidingAgainToGettingOut_inv: "AvoidingAgainToGettingOut() preserves Movement_inv"
  by (zpog_full; auto)
  
lemma GettingOutToGoing_inv: "GettingOutToGoing l preserves Movement_inv"
  by (zpog_full; auto)
  
lemma WaitingToWaiting_inv: "WaitingToWaiting() preserves Movement_inv"
  by (zpog_full; auto)
  
lemma WaitingToFound_inv: "WaitingToFound() preserves Movement_inv"
  by (zpog_full; auto)
  
lemma GettingOutToFound_inv: "GettingOutToFound() preserves Movement_inv"
  by (zpog_full; auto)
  
lemma AvoidingAgainToFound_inv: "AvoidingAgainToFound() preserves Movement_inv"
  by (zpog_full; auto)
  
lemma AvoidingToFound_inv: "AvoidingToFound() preserves Movement_inv"
  by (zpog_full; auto)
  
lemma AvoidingToWaiting_inv: "AvoidingToWaiting() preserves Movement_inv"
  by (zpog_full; auto)
  
lemma GettingOutToWaiting_inv: "GettingOutToWaiting() preserves Movement_inv"
  by (zpog_full; auto)
  
lemma AvoidingAgainToWaiting_inv: "AvoidingAgainToWaiting() preserves Movement_inv"
  by (zpog_full; auto)
  
lemma GoingToWaiting_inv: "GoingToWaiting() preserves Movement_inv"
  by (zpog_full; auto)
  

end

