abstract sig Event { 
	condition : set Event,
	response : set Event
}
sig Mark {
	executed : set Event, 
	toBeExecuted : set Event, 
	action : set Mark -> set Event
}
fact {
	all m,m': Mark, e : Event |
	(m -> m' -> e) in action <=> 
		(condition.e in m.executed and 
		m'.executed = m.executed + e and 
		m'.toBeExecuted = (m.toBeExecuted - e)
		+ e.response)
}


------------------------- a particular instance -------------------------

one sig PrescribeMed, SignDoc, PrepMed, GiveMed, SecEffect, ThEffect, FourEffect extends Event {}

fact {

	-- PrescibeMed has no condition events
	no condition.PrescribeMed
	-- PrescribeMed triggers GiveMed
	PrescribeMed.response = GiveMed + PrepMed + SignDoc

	-- PrescribeMed is the condition for SignDoc
	condition.SignDoc = PrescribeMed
	-- SignDoc triggers the PrepMed
	no SignDoc.response

	-- no condition for prepmed
	no condition.PrepMed
	-- PrepMed doens't trigger events
	no PrepMed.response


	-- To give medicine a signature must exist and it must be prepared
	condition.GiveMed = SignDoc + PrepMed
	-- GiveMed doens't trigger events
	no GiveMed.response

   SecEffect.response = PrescribeMed
   condition.SecEffect = GiveMed

	ThEffect.response = SecEffect
	condition.ThEffect = SecEffect	

	FourEffect.response = ThEffect
	condition.FourEffect = ThEffect	
}
--run {}
assert noExecuted {
	let transRun = ^(action.Event) |
		all m,m' : Mark |  
			( 	no m.(executed+toBeExecuted) and
				m' in m.transRun and 
				FourEffect in m'.executed and
				no m'.toBeExecuted ) 
			implies no m'.executed
}

check noExecuted for 12 Mark, 7 Event
