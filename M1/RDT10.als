module M1/RDT10

open util/ordering[State]

sig State {
	sender: one Sender,
	receiver: one Receiver,
	protocol: one Protocol
}
sig Protocol {
}

sig Stream {
	buffer: set Data
}
sig Sender extends Stream {}
sig Receiver extends Stream {}

sig Data {

}

pred Init[s: State] {
	#sender.buffer > 0
}

pred End[s: State] {
	first.sender.buffer in s.receiver.buffer
}

pred Transition[s, s': State] {
	one p: Position | (
		s'.board = s.board + p and 
		p not in s.board and 
		p.value in s.turn
	)
	s'.turn != s.turn
}

pred Trace {
	first.Init
	all s: State-last |
		let s' = s.next |
			Transition[s, s']
	last.End
}

