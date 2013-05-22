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


assert refRun {
	all m,m' : Mark, e : Event |
		m->m'->e in action and e in m'.toBeExecuted
			implies e in e.response
}
--check refRun for 10

------------------------- a particular instance -------------------------

one sig PrescribeMed, SignDoc, PrepMed, GiveMed, SecEffect  extends Event {}

fact {

	-- PrescibeMed has no condition events
	no condition.PrescribeMed
	-- PrescribeMed triggers GiveMed
	PrescribeMed.response = GiveMed + PrepMed + SignDoc

	-- The condition for SignDoc is PrescribeMed
	PrescribeMed = condition.SignDoc
	-- SignDoc triggers nothing
	no SignDoc.response

	-- The conditition for PrepMed is PrescribeMed
 	PrescribeMed =  condition.PrepMed
	-- PrepMed doens't trigger events
	no PrepMed.response


	-- To give medicine a signature must exist and it must be prepared
	condition.GiveMed = SignDoc + PrepMed
	-- GiveMed doens't trigger events
	no GiveMed.response

   SecEffect.response = PrescribeMed
   condition.SecEffect = GiveMed

	
}

assert noRef {
	 // there are no reflexive events
 all e : Event | not e in e.response
}
--check noRef for 5  Event, 10 Mark

-- Very hard to prove, when dealing with many events, as the scope must be bigger
assert noExecuted {
	let transRun = ^(action.Event) |
		all m,m' : Mark |  
			( 	no m.(executed+toBeExecuted) and
				m' in m.transRun and 
				SecEffect in m'.executed and
				no m'.toBeExecuted ) 
			implies no m'.executed
}

--check noExecuted for 16 Mark, 5 Event

assert badRun {
	no m,m' : Mark | no m.(executed+toBeExecuted) and m'.executed = Event and m->m' in action.Event
}
--check badRun for 5 Event, 10 Mark

assert noDeadlock {
	all e,e' : Event | not (e' in e.condition and e in e'.condition)
}
--check noDeadlock for 5 Event, 10 Mark

assert noDeadlockTrans {
 	let transCond = ^condition | 
		no e : Event | e in e.transCond 
}
--check noDeadlockTrans for 5 Event, 10 Mark

assert middleManTrans {
	let transRun = ^(action.Event) |
		all m,m' : Mark | ( no m.(executed+toBeExecuted)
			and SecEffect in m'.executed and
			m' in m.transRun ) => 
				(some m'' : Mark | 
					m'' in m.transRun and 
					m' in m''.transRun and 
					GiveMed in m'.executed)
}
--check middleManTrans for 5 Event, 10 Mark

run {}
