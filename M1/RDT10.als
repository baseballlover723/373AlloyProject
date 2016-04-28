module M1/RDT10

open util/ordering[State]

sig State {
	sender: one Sender,
	receiver: one Receiver,
	protocol: one Protocol
}

abstract sig Stream {
	buffer: set Data
}
one sig Sender extends Stream {}
one sig Receiver extends Stream {}

sig Data {
}

fact Reliable {
	no d: Data | d not in Sender.buffer + Receiver.buffer
}

pred Init[s: State] {
	#sender.buffer > 0
}

pred End[s: State] {
	first.sender.buffer in s.receiver.buffer
	#s.sender.buffer = 0
}

pred Transition[s, s': State] {
	
}

pred Trace {
	first.Init
	all s: State-last |
		let s' = s.next |
			Transition[s, s']
	last.End
}

run Trace for 1 State, exactly 5 Data, exactly 1 Protocol

run Init for 1 State, exactly 5 Data, exactly 1 Protocol
run End for 1 State, exactly 5 Data, exactly 1 Protocol


